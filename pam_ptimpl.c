/** BEGIN COPYRIGHT BLOCK
 * This Program is free software; you can redistribute it and/or modify it under
 * the terms of the GNU General Public License as published by the Free Software
 * Foundation; version 2 of the License.
 * 
 * This Program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along with
 * this Program; if not, write to the Free Software Foundation, Inc., 59 Temple
 * Place, Suite 330, Boston, MA 02111-1307 USA.
 * 
 * In addition, as a special exception, Red Hat, Inc. gives You the additional
 * right to link the code of this Program with code not covered under the GNU
 * General Public License ("Non-GPL Code") and to distribute linked combinations
 * including the two, subject to the limitations in this paragraph. Non-GPL Code
 * permitted under this exception must only link to the code of this Program
 * through those well defined interfaces identified in the file named EXCEPTION
 * found in the source code files (the "Approved Interfaces"). The files of
 * Non-GPL Code may instantiate templates or use macros or inline functions from
 * the Approved Interfaces without causing the resulting work to be covered by
 * the GNU General Public License. Only Red Hat, Inc. may make changes or
 * additions to the list of Approved Interfaces. You must obey the GNU General
 * Public License in all respects for all of the Program code and other code used
 * in conjunction with the Program except the Non-GPL Code covered by this
 * exception. If you modify this file, you may extend this exception to your
 * version of the file, but you are not obligated to do so. If you do not wish to
 * provide this exception without modification, you must delete this exception
 * statement from your version and license this file solely under the GPL without
 * exception. 
 * 
 * 
 * Copyright (C) 2005 Red Hat, Inc.
 * All rights reserved.
 * END COPYRIGHT BLOCK **/

#include <security/pam_appl.h>
#include <pk11func.h>
#include <nss.h>
#include <nssb64.h>
#include "slap.h"

#include "pam_passthru.h"


/*
 * PAM is not thread safe.  We have to execute any PAM API calls in
 * a critical section.  This is the lock that protects that code.
 */
static Slapi_Mutex *PAMLock;
static Slapi_Mutex *PAMCondLock;
static Slapi_CondVar *PAMCond;
static int pam_in_use;

/* Utility struct to wrap strings to avoid mallocs if possible - use
   stack allocated string space */
#define MY_STATIC_BUF_SIZE 256
typedef struct my_str_buf {
	char fixbuf[MY_STATIC_BUF_SIZE];
	char *str;
} MyStrBuf;

static char *
init_my_str_buf(MyStrBuf *buf, const char *s)
{
	PR_ASSERT(buf);
	if (s && (strlen(s) < sizeof(buf->fixbuf))) {
		strcpy(buf->fixbuf, s);
		buf->str = buf->fixbuf;
	} else {
		buf->str = slapi_ch_strdup(s);
		buf->fixbuf[0] = 0;
	}

	return buf->str;
}

static void
delete_my_str_buf(MyStrBuf *buf)
{
	if (buf->str != buf->fixbuf) {
		slapi_ch_free_string(&buf->str);
	}
}

/* for third arg to pam_start */
struct my_pam_conv_str {
	Slapi_PBlock *pb;
	char *pam_identity;
};

/*
 * Get the PAM identity from the value of the leftmost RDN in the BIND DN.
 */
static char *
derive_from_bind_dn(Slapi_PBlock *pb, char *binddn, MyStrBuf *pam_id)
{
	Slapi_RDN *rdn;
	char *type = NULL;
	char *value = NULL;

	rdn = slapi_rdn_new_dn(binddn);
	slapi_rdn_get_first(rdn, &type, &value);
	init_my_str_buf(pam_id, value);
	slapi_rdn_free(&rdn);

	return pam_id->str;
}

static char *
derive_from_bind_entry(Slapi_PBlock *pb, char *binddn, MyStrBuf *pam_id, char *map_ident_attr,
		       MyStrBuf *pam_service, char *map_service_attr)
{
	char buf[BUFSIZ];
	Slapi_Entry *entry = NULL;
	Slapi_DN *sdn = slapi_sdn_new_dn_byref(binddn);
	char *attrs[] = { NULL, NULL, NULL };
	attrs[0] = map_ident_attr;
	attrs[1] = map_service_attr;
	int rc = slapi_search_internal_get_entry(sdn, attrs, &entry,
						 pam_passthruauth_get_plugin_identity());
	slapi_sdn_free(&sdn);

	if (rc != LDAP_SUCCESS) {
		slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
				"Could not find BIND dn %s (error %d - %s)\n",
				escape_string(binddn, buf), rc, ldap_err2string(rc));
		init_my_str_buf(pam_id, NULL);
		init_my_str_buf(pam_service, NULL);
   	} else if (NULL == entry) {
		slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
				"Could not find entry for BIND dn %s\n",
				escape_string(binddn, buf));
		init_my_str_buf(pam_id, NULL);
		init_my_str_buf(pam_service, NULL);
	} else {
		char *val = slapi_entry_attr_get_charptr(entry, map_ident_attr);
		init_my_str_buf(pam_id, val);
		slapi_ch_free_string(&val);
		val = slapi_entry_attr_get_charptr(entry, map_service_attr);
		init_my_str_buf(pam_service, val);
		slapi_ch_free_string(&val);
	}

	slapi_entry_free(entry);

	return pam_id->str;
}


/* need_new_pw() is called when non rootdn bind operation succeeds with authentication */ 
static int
_pam_need_new_pw( Slapi_PBlock *pb, long *t, Slapi_Entry *e, int pwresponse_req )
{
	time_t 		cur_time, pw_exp_date;
 	LDAPMod 	*mod;
	Slapi_Mods smods;
	double		diff_t = 0;
	char 		*cur_time_str = NULL;
	char *passwordExpirationTime;
	char *timestring;
	char *dn;
	passwdPolicy *pwpolicy = NULL;
	int	pwdGraceUserTime = 0;
	char graceUserTime[8];

	slapi_mods_init (&smods, 0);
	dn = slapi_entry_get_ndn( e );
	pwpolicy = new_passwdPolicy(pb, dn);

	/* after the user binds with authentication, clear the retry count */
	if ( pwpolicy->pw_lockout == 1)
	{
		if(slapi_entry_attr_get_int( e, "passwordRetryCount") > 0)
		{
			slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordRetryCount", "0");
		}
	}

	cur_time = current_time();

	/* get passwordExpirationTime attribute */
	passwordExpirationTime= slapi_entry_attr_get_charptr(e, "passwordExpirationTime");

	if (passwordExpirationTime == NULL)
	{
		/* password expiration date is not set.
		 * This is ok for data that has been loaded via ldif2ldbm
		 * Set expiration time if needed,
		 * don't do further checking and return 0 */
		if ( pwpolicy->pw_exp == 1) {
			pw_exp_date = time_plus_sec ( cur_time, 
				pwpolicy->pw_maxage );

			timestring = format_genTime (pw_exp_date);			
			slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpirationTime", timestring);
			slapi_ch_free((void **)&timestring);
			slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpWarned", "0");
			
			pw_apply_mods(dn, &smods);
		}
		slapi_mods_done(&smods);
		delete_passwdPolicy(&pwpolicy);
		return ( 0 );
	}

	pw_exp_date = parse_genTime(passwordExpirationTime);

        slapi_ch_free((void**)&passwordExpirationTime);

	/* Check if password has been reset */
	if ( pw_exp_date == NO_TIME ) {

		/* check if changing password is required */  
		if ( pwpolicy->pw_must_change ) {
			/* set c_needpw for this connection to be true.  this client 
			   now can only change its own password */
			pb->pb_conn->c_needpw = 1;
			*t=0;
			/* We need to include "changeafterreset" error in
			 * passwordpolicy response control. So, we will not be
			 * done here. We remember this scenario by (c_needpw=1)
			 * and check it before sending the control from various
			 * places. We will also add LDAP_CONTROL_PWEXPIRED control
			 * as the return value used to be (1).
			 */
			goto skip;
		}
		/* Mark that first login occured */
		pw_exp_date = NOT_FIRST_TIME;
		timestring = format_genTime(pw_exp_date);
		slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpirationTime", timestring);
		slapi_ch_free((void **)&timestring);
	}

skip:
	/* if password never expires, don't need to go on; return 0 */
	if ( pwpolicy->pw_exp == 0 ) {
		/* check for "changeafterreset" condition */
		if (pb->pb_conn->c_needpw == 1) {
			if (pwresponse_req) {
				slapi_pwpolicy_make_response_control ( pb, -1, -1, LDAP_PWPOLICY_CHGAFTERRESET );
			} 
			slapi_add_pwd_control ( pb, LDAP_CONTROL_PWEXPIRED, 0);
		}
		pw_apply_mods(dn, &smods);
		slapi_mods_done(&smods);
		delete_passwdPolicy(&pwpolicy);
		return ( 0 );
	}

	/* check if password expired.  If so, abort bind. */
	cur_time_str = format_genTime ( cur_time );
	if ( pw_exp_date != NO_TIME  && 
		 pw_exp_date != NOT_FIRST_TIME && 
		 (diff_t = difftime ( pw_exp_date, 
			parse_genTime ( cur_time_str ))) <= 0 ) {
	
		slapi_ch_free_string(&cur_time_str); /* only need this above */
		/* password has expired. Check the value of 
		 * passwordGraceUserTime and compare it
		 * against the value of passwordGraceLimit */
		pwdGraceUserTime = slapi_entry_attr_get_int( e, "passwordGraceUserTime");
		if ( pwpolicy->pw_gracelimit > pwdGraceUserTime ) {
			pwdGraceUserTime++;
			sprintf ( graceUserTime, "%d", pwdGraceUserTime );
			slapi_mods_add_string(&smods, LDAP_MOD_REPLACE,
				"passwordGraceUserTime", graceUserTime);	
			pw_apply_mods(dn, &smods);
			slapi_mods_done(&smods);
			if (pwresponse_req) {
				/* check for "changeafterreset" condition */
				if (pb->pb_conn->c_needpw == 1) {
					slapi_pwpolicy_make_response_control( pb, -1, 
						((pwpolicy->pw_gracelimit) - pwdGraceUserTime),
						LDAP_PWPOLICY_CHGAFTERRESET);
				} else {
					slapi_pwpolicy_make_response_control( pb, -1, 
						((pwpolicy->pw_gracelimit) - pwdGraceUserTime),
						-1);
				}
			}
			
			if (pb->pb_conn->c_needpw == 1) {
				slapi_add_pwd_control ( pb, LDAP_CONTROL_PWEXPIRED, 0);
			}
			delete_passwdPolicy(&pwpolicy);
			return ( 0 );
		}

		/* password expired and user exceeded limit of grace attemps.
		 * Send result and also the control */
		slapi_add_pwd_control ( pb, LDAP_CONTROL_PWEXPIRED, 0);
		if (pwresponse_req) {
			slapi_pwpolicy_make_response_control ( pb, -1, -1, LDAP_PWPOLICY_PWDEXPIRED );
		}
		slapi_send_ldap_result ( pb, LDAP_INVALID_CREDENTIALS, NULL,
			"password expired!", 0, NULL );
		
		/* abort bind */
		/* pass pb to do_unbind().  pb->pb_op->o_opid and 
		   pb->pb_op->o_tag are not right but I don't see 
		   do_unbind() checking for those.   We might need to 
		   create a pb for unbind operation.  Also do_unbind calls
		   pre and post ops.  Maybe we don't want to call them */
		if (pb->pb_conn && (LDAP_VERSION2 == pb->pb_conn->c_ldapversion)) {
			/* We close the connection only with LDAPv2 connections */
			do_unbind( pb );
		}
		/* Apply current modifications */
		pw_apply_mods(dn, &smods);
		slapi_mods_done(&smods);
		delete_passwdPolicy(&pwpolicy);
		return (-1);
	} 
	slapi_ch_free((void **) &cur_time_str );

	/* check if password is going to expire within "passwordWarning" */
	/* Note that if pw_exp_date is NO_TIME or NOT_FIRST_TIME,
	 * we must send warning first and this changes the expiration time.
	 * This is done just below since diff_t is 0 
  	 */
	if ( diff_t <= pwpolicy->pw_warning ) {
		int pw_exp_warned = 0;
		
		pw_exp_warned= slapi_entry_attr_get_int( e, "passwordExpWarned");
		if ( !pw_exp_warned ){
			/* first time send out a warning */
			/* reset the expiration time to current + warning time 
			 * and set passwordExpWarned to true
			 */
			if (pb->pb_conn->c_needpw != 1) {
				pw_exp_date = time_plus_sec ( cur_time, 
					pwpolicy->pw_warning );
			}
			
			timestring = format_genTime(pw_exp_date);
			/* At this time passwordExpirationTime may already be
			 * in the list of mods: Remove it */
			for (mod = slapi_mods_get_first_mod(&smods); mod != NULL; 
				 mod = slapi_mods_get_next_mod(&smods))
			{
				if (!strcmp(mod->mod_type, "passwordExpirationTime"))
					slapi_mods_remove(&smods);
			}

			slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpirationTime", timestring);
			slapi_ch_free((void **)&timestring);

			slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpWarned", "1");
			
			*t = pwpolicy->pw_warning;

		} else {
			*t = (long)diff_t; /* jcm: had to cast double to long */
		}
			
		pw_apply_mods(dn, &smods);
		slapi_mods_done(&smods);
		if (pwresponse_req) {
			/* check for "changeafterreset" condition */
			if (pb->pb_conn->c_needpw == 1) {
					slapi_pwpolicy_make_response_control( pb, *t, -1,
						LDAP_PWPOLICY_CHGAFTERRESET);
				} else {
					slapi_pwpolicy_make_response_control( pb, *t, -1,
						-1);
				}
		}

		if (pb->pb_conn->c_needpw == 1) {
			slapi_add_pwd_control ( pb, LDAP_CONTROL_PWEXPIRED, 0);
		}
		delete_passwdPolicy(&pwpolicy);
		return (2);
	}

	pw_apply_mods(dn, &smods);
	slapi_mods_done(&smods);
	/* Leftover from "changeafterreset" condition */
	if (pb->pb_conn->c_needpw == 1) {
		slapi_add_pwd_control ( pb, LDAP_CONTROL_PWEXPIRED, 0);
	}
	delete_passwdPolicy(&pwpolicy);
	/* passes checking, return 0 */
	return( 0 );
}

/* check_account_lock is called before bind opeation; this could be a pre-op. */
static int
_pam_check_account_lock ( Slapi_PBlock *pb, Slapi_Entry * bind_target_entry, int pwresponse_req) {

	time_t		unlock_time;
	time_t		cur_time;
	double		diff_t;
	char		*cur_time_str = NULL;
	char *accountUnlockTime;
	passwdPolicy *pwpolicy = NULL;
	char *dn = NULL;

	/* kexcoff: account inactivation */
	int rc = 0;
	Slapi_ValueSet *values = NULL;
	int type_name_disposition = 0;
	char *actual_type_name = NULL;
	int attr_free_flags = 0;
	/* kexcoff - end */

	if ( bind_target_entry == NULL ) 
		return -1;

	dn = slapi_entry_get_ndn(bind_target_entry);
	pwpolicy = new_passwdPolicy(pb, dn);

	/* kexcoff: account inactivation */
	/* check if the entry is locked by nsAccountLock attribute - account inactivation feature */

	rc = slapi_vattr_values_get(bind_target_entry, "nsAccountLock", 
								&values, 
								&type_name_disposition, &actual_type_name,
								SLAPI_VIRTUALATTRS_REQUEST_POINTERS,
								&attr_free_flags);
	if ( rc == 0 )
	{
		Slapi_Value *v = NULL;	
		const struct berval *bvp = NULL;

		if ( (slapi_valueset_first_value( values, &v ) != -1) &&
				( bvp = slapi_value_get_berval( v )) != NULL )
		{
			if ( (bvp != NULL) && (strcasecmp(bvp->bv_val, "true") == 0) )
			{
				/* account inactivated */
				if (pwresponse_req) {
					slapi_pwpolicy_make_response_control ( pb, -1, -1,
							LDAP_PWPOLICY_ACCTLOCKED );
				}
				send_ldap_result ( pb, LDAP_UNWILLING_TO_PERFORM, NULL,
							"Account inactivated. Contact system administrator.",
							0, NULL );
				slapi_vattr_values_free(&values, &actual_type_name, attr_free_flags);
				goto locked;
			}
		} /* else, account "activated", keep on the process */

		if ( values != NULL )
			slapi_vattr_values_free(&values, &actual_type_name, attr_free_flags);
	}
	/* kexcoff - end */

	/*
	 * Check if the password policy has to be checked or not
	 */
	if ( pwpolicy->pw_lockout == 0 ) {
		goto notlocked;
	}

	/*
	 * Check the attribute of the password policy
	 */

	/* check if account is locked out.  If so, send result and return 1 */
	{
		unsigned int maxfailure= pwpolicy->pw_maxfailure;
		/* It's locked if passwordRetryCount >= maxfailure */
		if ( slapi_entry_attr_get_uint(bind_target_entry,"passwordRetryCount") < maxfailure )
		{
			/* Not locked */
			goto notlocked;	
		}
	}

	/* locked but maybe it's time to unlock it */
	accountUnlockTime= slapi_entry_attr_get_charptr(bind_target_entry, "accountUnlockTime");
	if (accountUnlockTime != NULL)
	{
		unlock_time = parse_genTime(accountUnlockTime);
		slapi_ch_free((void **) &accountUnlockTime );

		if ( pwpolicy->pw_unlock == 0 && 
			unlock_time == NO_TIME ) {

	        /* account is locked forever. contact admin to reset */
			if (pwresponse_req) {
				slapi_pwpolicy_make_response_control ( pb, -1, -1,
						LDAP_PWPOLICY_ACCTLOCKED );
			}
	        send_ldap_result ( pb, LDAP_CONSTRAINT_VIOLATION, NULL,
	                "Exceed password retry limit. Contact system administrator to reset."
	                , 0, NULL );
			goto locked;
		}
		cur_time = current_time();
		cur_time_str = format_genTime( cur_time);
		if ( ( diff_t = difftime ( parse_genTime( cur_time_str ), 
			unlock_time ) ) < 0 ) {

			/* account is locked, cannot do anything */	
			if (pwresponse_req) {
				slapi_pwpolicy_make_response_control ( pb, -1, -1,
						LDAP_PWPOLICY_ACCTLOCKED );
			}
			send_ldap_result ( pb, LDAP_CONSTRAINT_VIOLATION, NULL,
				"Exceed password retry limit. Please try later."				, 0, NULL );
			slapi_ch_free((void **) &cur_time_str );
			goto locked;
		} 
		slapi_ch_free((void **) &cur_time_str );
	}

notlocked:
	/* account is not locked. */ 
	delete_passwdPolicy(&pwpolicy);
	return ( 0 );	
locked:
	delete_passwdPolicy(&pwpolicy);
	return (1);

}

static int
do_weakpw_auth(Slapi_PBlock *pb, char *binddn, int pw_response_requested) 
{
	char buf[BUFSIZ];
	char *weakpw = NULL;
	Slapi_Entry *entry = NULL;
	Slapi_DN *sdn = slapi_sdn_new_dn_byref(binddn);;
	char *attrs[] = { NULL, NULL, NULL };
	attrs[0] = "cuniweakuserpassword";
	
	int rc = slapi_search_internal_get_entry(sdn, NULL, &entry, 
						 pam_passthruauth_get_plugin_identity());
	slapi_sdn_free(&sdn);
	if(rc != LDAP_SUCCESS) {
		slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
				"Could not find BIND dn %s\n",
				escape_string(binddn, buf));
		goto loser;
	} else if(NULL == entry) {
		slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
				"Could not find entry for BIND dn %s\n",
				escape_string(binddn, buf));
		goto loser;
	} else {
		weakpw = slapi_entry_attr_get_charptr(entry, "cuniweakuserpassword");
		if(NULL == weakpw) {
			slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
					"Entry %s has no weak password attribute\n",
					escape_string(binddn, buf));
			rc = LDAP_NO_SUCH_ATTRIBUTE;
			goto loser;
		}
	}

	/* no fallback in this case */
	rc = _pam_check_account_lock(pb, entry, pw_response_requested);
	/*				
	 * rc=0 (LDAP_SUCCESS): account not locked
	 * rc=1 (LDAP_OPERATIONS_ERROR): account locked, can not bind, result has been sent 
	 * rc!=0 and rc!=1: error. Result was not sent, let the fallback
	 *          deal with it.
	 */
	switch(rc) {
	case 0: 
		break;
		
	case 1:
		rc = LDAP_UNWILLING_TO_PERFORM;
		break;
		
	default:
		rc = LDAP_OPERATIONS_ERROR;
		break;
	}
	if(rc) 
		goto loser;

	/* going to verify password */
	struct berval *creds = NULL;
	slapi_pblock_get(pb, SLAPI_BIND_CREDENTIALS, &creds ); /* the password */
	/* compare MD5 hash of the given credentials with stored password */
	if(creds) {
#define MD5_HASH_LEN 20
		rc=LDAP_OPERATIONS_ERROR;
		char * bver;
		PK11Context *ctx=NULL;
		unsigned int outLen;
		unsigned char hash_out[MD5_HASH_LEN];
		unsigned char b2a_out[MD5_HASH_LEN*2]; /* conservative */
		SECItem binary_item;
		
		ctx = PK11_CreateDigestContext(SEC_OID_MD5);
		if (ctx == NULL) {
			slapi_log_error(SLAPI_LOG_PLUGIN, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
					"Could not create context for digest operation for password compare");
			goto loser;
		}
		
		/* create the hash */
		PK11_DigestBegin(ctx);
		PK11_DigestOp(ctx, creds->bv_val, creds->bv_len);
		PK11_DigestFinal(ctx, hash_out, &outLen, sizeof hash_out);
		PK11_DestroyContext(ctx, 1);
		
		/* convert the binary hash to base64 */
		binary_item.data = hash_out;
		binary_item.len = outLen;
		bver = NSSBase64_EncodeItem(NULL, b2a_out, sizeof b2a_out, &binary_item);
		/* bver points to b2a_out upon success */
		if (bver) {
			if(strcmp(bver, weakpw)) {
				rc = LDAP_INVALID_CREDENTIALS;
				/* we are going to fallback to simple bind, account lock will be checked there */
			} else {
				long t;

				switch(_pam_need_new_pw(pb, &t, entry, pw_response_requested)) {
				case 1:
					rc = LDAP_UNWILLING_TO_PERFORM;
					break;
                                                
				case 2:
					break;

				case -1: 
					rc = LDAP_OPERATIONS_ERROR;
					goto loser;

				default:
					break;
				} 

			}
		} else {
			slapi_log_error(SLAPI_LOG_PLUGIN, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
					"Could not base64 encode hashed value for password compare");
		}
	} else {
		rc = LDAP_OPERATIONS_ERROR;
	}

loser:
	if(entry) { slapi_entry_free(entry); }
	slapi_ch_free_string(&weakpw);
	return rc;
}

static void
report_pam_error(char *str, int rc, pam_handle_t *pam_handle)
{
	if (rc != PAM_SUCCESS) {
		slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
				"Error from PAM %s (%d: %s)\n",
				str, rc, pam_strerror(pam_handle, rc));
	}
}

/* returns a berval value as a null terminated string */
static char *strdupbv(struct berval *bv)
{
	char *str = malloc(bv->bv_len+1);
	memcpy(str, bv->bv_val, bv->bv_len);
	str[bv->bv_len] = 0;
	return str;
}

static void
free_pam_response(int nresp, struct pam_response *resp)
{
	int ii;
	for (ii = 0; ii < nresp; ++ii) {
		if (resp[ii].resp) {
			free(resp[ii].resp);
		}
	}
	free(resp);
}

/*
 * This is the conversation function passed into pam_start().  This is what sets the password
 * that PAM uses to authenticate.  This function is sort of stupid - it assumes all echo off
 * or binary prompts are for the password, and other prompts are for the username.  Time will
 * tell if this is actually the case.
 */
static int
pam_conv_func(int num_msg, const struct pam_message **msg, struct pam_response **resp, void *mydata)
{
	int ii;
	struct berval *creds;
	struct my_pam_conv_str *my_data = (struct my_pam_conv_str *)mydata;
	struct pam_response *reply;
	int ret = PAM_SUCCESS;

	if (num_msg <= 0) {
		return PAM_CONV_ERR;
	}

	/* empty reply structure */
	reply = (struct pam_response *)calloc(num_msg,sizeof(struct pam_response));
	if(!reply) {
		slapi_log_error(SLAPI_LOG_PLUGIN, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
				"error allocating PAM reply\n");
		return PAM_CONV_ERR;
	}
	slapi_pblock_get( my_data->pb, SLAPI_BIND_CREDENTIALS, &creds ); /* the password */
	for (ii = 0; ii < num_msg; ++ii) {
		slapi_log_error(SLAPI_LOG_PLUGIN, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
				"pam msg [%d] = %d %s\n", ii, msg[ii]->msg_style,
				msg[ii]->msg);

		reply[ii].resp_retcode = 0;

		/* hard to tell what prompt is for . . . */
		/* assume prompts for password are either BINARY or ECHO_OFF */
		switch(msg[ii]->msg_style) {
		case PAM_PROMPT_ECHO_OFF:
			reply[ii].resp = strdupbv(creds);
			break;

#ifdef LINUX
		case PAM_BINARY_PROMPT:
			/* XXX - this is definitely wrong way to do that 
			   reply[ii].resp = strdupbv(creds); */
			break;
#endif

		case PAM_PROMPT_ECHO_ON:
			reply[ii].resp = strdup(my_data->pam_identity);
			break;

		case PAM_ERROR_MSG:
			slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
					"pam msg [%d] error [%s]\n", ii, msg[ii]->msg);
			break;

		case PAM_TEXT_INFO:
			slapi_log_error(SLAPI_LOG_PLUGIN, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
					"pam msg [%d] text info [%s]\n", ii, msg[ii]->msg);
			break;

		default:
			slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
					"Error: unknown pam message type (%d: %s)\n",
					msg[ii]->msg_style, msg[ii]->msg);
			ret = PAM_CONV_ERR;
			break;
		}
	}

	if (ret == PAM_CONV_ERR) {
		free_pam_response(num_msg, reply);
		reply = NULL;
	}

	*resp = reply;

	return ret;
}

/*
 * Do the actual work of authenticating with PAM. First, get the PAM identity
 * based on the method used to convert the BIND identity to the PAM identity.
 * Set up the structures that pam_start needs and call pam_start().  After
 * that, call pam_authenticate and pam_acct_mgmt.  Check the various return
 * values from these functions and map them to their corresponding LDAP BIND
 * return values.  Return the appropriate LDAP error code.
 * This function will also set the appropriate LDAP response controls in
 * the given pblock.
 * Since this function can be called multiple times, we only want to return
 * the errors and controls to the user if this is the final call, so the
 * final_method parameter tells us if this is the last one.  Coupled with
 * the fallback argument, we can tell if we are able to send the response
 * back to the client.
 */
static int
do_one_pam_auth(
	Slapi_PBlock *pb,
	int method, /* get pam identity from ENTRY, RDN, or DN */
	PRBool final_method, /* which method is the last one to try */
	char *pam_service, /* default name of service for pam_start() */
	char *map_ident_attr, /* for ENTRY method, name of attribute holding pam identity */
	char *map_service_attr, /* for ENTRY method, name of pam service to check */
	PRBool fallback, /* if true, failure here should fallback to regular bind */
	int pw_response_requested /* do we need to send pwd policy resp control */
)
{
	MyStrBuf pam_id, my_pam_service;
	char *binddn = NULL;
	int rc;
	int retcode = LDAP_SUCCESS;
	pam_handle_t *pam_handle;
	struct my_pam_conv_str my_data;
	struct pam_conv my_pam_conv = {pam_conv_func, NULL};
	char buf[BUFSIZ]; /* for error messages */
	char *errmsg = NULL; /* free with PR_smprintf_free */
	int result_sent = 0;

	slapi_pblock_get( pb, SLAPI_BIND_TARGET, &binddn );

	init_my_str_buf(&my_pam_service, NULL);
	if (method == PAMPT_MAP_METHOD_RDN) {
		derive_from_bind_dn(pb, binddn, &pam_id);
	} else if (method == PAMPT_MAP_METHOD_ENTRY) {
		derive_from_bind_entry(pb, binddn, &pam_id, map_ident_attr, &my_pam_service, map_service_attr);
	} else {
		init_my_str_buf(&pam_id, binddn);
	}
	if(my_pam_service.str) {
		pam_service = my_pam_service.str;
	}
	if(strcmp(pam_service, "weakpassword") == 0) {
		/* ugly site-specific hack for one specific pam service, which is not pam at all*/
		retcode = do_weakpw_auth(pb, binddn, pw_response_requested);
		if(LDAP_SUCCESS == retcode) {
			errmsg = PR_smprintf("Weak password authentication for DN %s successful", binddn);
		} else if(LDAP_UNWILLING_TO_PERFORM == retcode) {
			errmsg = PR_smprintf("Weak password authentication for DN %s:  account locked", binddn);
			result_sent = 1;
		} else {
			errmsg = PR_smprintf("Weak password authentication for DN %s failed", binddn);
		}
		goto done;
	}
	if(!pam_id.str) {
		errmsg = PR_smprintf("PAM id for DN [%s] does not exist", binddn);
		retcode = LDAP_NO_SUCH_OBJECT;
		goto done;
	}

	/* do the pam stuff */
	my_data.pb = pb;
	my_data.pam_identity = pam_id.str;
	my_pam_conv.appdata_ptr = &my_data;

	/* avoid blocking threads on PAMLock, give it a try and bail out if other thread 
	   is holding the lock */
	slapi_lock_mutex(PAMCondLock);
	/* if pam is in use, wait */
	if(pam_in_use) {
		struct timeval tv;
		tv.tv_sec = 30;
		tv.tv_usec = 0;
		slapi_wait_condvar(PAMCond, &tv);
	}
	/* if PAM is still locked, bail out */
	if(pam_in_use) {
		errmsg = PR_smprintf("PAM is blocked by another thread for more than 30 seconds, giving up");
		retcode = LDAP_OPERATIONS_ERROR;
		slapi_unlock_mutex(PAMCondLock);
		goto done;
	}
	pam_in_use = 1;
	slapi_unlock_mutex(PAMCondLock);

        slapi_lock_mutex(PAMLock);
	/* from this point on we are in the critical section */
	rc = pam_start(pam_service, pam_id.str, &my_pam_conv, &pam_handle);
	report_pam_error("during pam_start", rc, pam_handle);

	if (rc == PAM_SUCCESS) {
		/* use PAM_SILENT - there is no user interaction at this point */
		rc = pam_authenticate(pam_handle, 0);
		report_pam_error("during pam_authenticate", rc, pam_handle);
		/* check different types of errors here */
		switch(rc) {
		case  PAM_USER_UNKNOWN:
			errmsg = PR_smprintf("User id [%s] for bind DN [%s] does not exist in PAM",
					     pam_id.str, escape_string(binddn, buf));
			retcode = LDAP_NO_SUCH_OBJECT; /* user unknown */
			break;

		case PAM_AUTH_ERR:
			errmsg = PR_smprintf("Invalid PAM password for user id [%s], bind DN [%s]",
					     pam_id.str, escape_string(binddn, buf));
			retcode = LDAP_INVALID_CREDENTIALS; /* invalid creds */
			break;

		case PAM_MAXTRIES:
			errmsg = PR_smprintf("Authentication retry limit exceeded in PAM for "
					     "user id [%s], bind DN [%s]",
					     pam_id.str, escape_string(binddn, buf));
			if (pw_response_requested) {
				slapi_pwpolicy_make_response_control(pb, -1, -1, LDAP_PWPOLICY_ACCTLOCKED);
			}
			retcode = LDAP_CONSTRAINT_VIOLATION; /* max retries */
			break;

		case PAM_SUCCESS:
			break;

		default:
			errmsg = PR_smprintf("Unknown PAM error [%s] for user id [%s], bind DN [%s]",
					     pam_strerror(pam_handle, rc), pam_id.str, escape_string(binddn, buf));
			retcode = LDAP_OPERATIONS_ERROR; /* pam config or network problem */
		}
	}

	/* if user authenticated successfully, see if there is anything we need
	   to report back w.r.t. password or account lockout */
	if (rc == PAM_SUCCESS) {
		rc = pam_acct_mgmt(pam_handle, 0);
		report_pam_error("during pam_acct_mgmt", rc, pam_handle);
		/* check different types of errors here */
		switch(rc) {
		case PAM_USER_UNKNOWN:
			errmsg = PR_smprintf("User id [%s] for bind DN [%s] does not exist in PAM",
					     pam_id.str, escape_string(binddn, buf));
			retcode = LDAP_NO_SUCH_OBJECT; /* user unknown */
			break;

		case PAM_AUTH_ERR:
			errmsg = PR_smprintf("Invalid PAM password for user id [%s], bind DN [%s]",
					     pam_id.str, escape_string(binddn, buf));
			retcode = LDAP_INVALID_CREDENTIALS; /* invalid creds */
			break;

		case PAM_PERM_DENIED:
			errmsg = PR_smprintf("Access denied for PAM user id [%s], bind DN [%s]"
					     " - see administrator",
					     pam_id.str, escape_string(binddn, buf));
			if (pw_response_requested) {
				slapi_pwpolicy_make_response_control(pb, -1, -1, LDAP_PWPOLICY_ACCTLOCKED);
			}
			retcode = LDAP_UNWILLING_TO_PERFORM;
			break;

		case PAM_NEW_AUTHTOK_REQD:
		case PAM_ACCT_EXPIRED:
			errmsg = PR_smprintf("Expired PAM password for user id [%s], bind DN [%s]: "
					     "reset required",
					     pam_id.str, escape_string(binddn, buf));
			slapi_add_pwd_control(pb, LDAP_CONTROL_PWEXPIRED, 0);
			if (pw_response_requested) {
				slapi_pwpolicy_make_response_control(pb, -1, -1, LDAP_PWPOLICY_PWDEXPIRED);
			}
			retcode = LDAP_INVALID_CREDENTIALS;
			break;

		case PAM_SUCCESS:
			break;

		default:
			errmsg = PR_smprintf("Unknown PAM error [%s] for user id [%s], bind DN [%s]",
					     pam_strerror(pam_handle, rc), pam_id.str, escape_string(binddn, buf));
			retcode = LDAP_OPERATIONS_ERROR; /* unknown */
		}
	}

	rc = pam_end(pam_handle, rc);
	report_pam_error("during pam_end", rc, pam_handle);

	slapi_unlock_mutex(PAMLock);
	/* not in critical section any more */

	slapi_lock_mutex(PAMCondLock);
	pam_in_use = 0;
	slapi_notify_condvar(PAMCond, 0);
	slapi_unlock_mutex(PAMCondLock);


	if ((retcode == LDAP_SUCCESS) && (rc != PAM_SUCCESS)) {
		errmsg = PR_smprintf("Unknown PAM error [%d] for user id [%d], bind DN [%s]",
				     rc, pam_id.str, escape_string(binddn, buf));
		retcode = LDAP_OPERATIONS_ERROR;
	}
done:
	delete_my_str_buf(&pam_id);
	delete_my_str_buf(&my_pam_service);
	if (retcode != LDAP_SUCCESS) {
		slapi_log_error(SLAPI_LOG_FATAL, PAM_PASSTHRU_PLUGIN_SUBSYSTEM,
						"%s\n", errmsg);
		if (final_method && !fallback && !result_sent) {
			slapi_send_ldap_result(pb, retcode, NULL, errmsg, 0, NULL);
		}
	}

	if (errmsg) {
		PR_smprintf_free(errmsg);
	}

	return retcode;
}

/*
 * Perform any PAM subsystem initialization that must be done at startup time.
 * For now, this means only the PAM mutex since PAM is not thread safe.
 */
int
pam_passthru_pam_init( void )
{
	if (!(PAMLock = slapi_new_mutex())) {
		return LDAP_LOCAL_ERROR;
	}
	if (!(PAMCondLock = slapi_new_mutex())) {
		return LDAP_LOCAL_ERROR;
	}
	if (!(PAMCond = slapi_new_condvar(PAMCondLock))) {
		return LDAP_LOCAL_ERROR;
	}
	pam_in_use = 0;

	return 0;
}

/*
 * Entry point into the PAM auth code.  Shields the rest of the app
 * from PAM API code.  Get our config params, then call the actual
 * code that does the PAM auth.  Can call that code up to 3 times,
 * depending on what methods are set in the config.
 */
int
pam_passthru_do_pam_auth(Slapi_PBlock *pb, Pam_PassthruConfig *cfg)
{
	int rc = LDAP_SUCCESS;
	MyStrBuf pam_id_attr; /* avoid malloc if possible */
	MyStrBuf pam_service; /* avoid malloc if possible */
	MyStrBuf pam_service_attr; 
	int method1, method2, method3;
	PRBool final_method;
	PRBool fallback = PR_FALSE;
	int pw_response_requested;
	LDAPControl **reqctrls = NULL;

	/* first lock and get the methods and other info */
	/* we do this so we can acquire and release the lock quickly to
	   avoid potential deadlocks */
	slapi_lock_mutex(cfg->lock);
	method1 = cfg->pamptconfig_map_method1;
	method2 = cfg->pamptconfig_map_method2;
	method3 = cfg->pamptconfig_map_method3;

	init_my_str_buf(&pam_id_attr, cfg->pamptconfig_pam_ident_attr);
	init_my_str_buf(&pam_service, cfg->pamptconfig_service);
	init_my_str_buf(&pam_service_attr, cfg->pamptconfig_service_attr);

	fallback = cfg->pamptconfig_fallback;

	slapi_unlock_mutex(cfg->lock);

	slapi_pblock_get (pb, SLAPI_REQCONTROLS, &reqctrls);
	slapi_pblock_get (pb, SLAPI_PWPOLICY, &pw_response_requested);

	/* figure out which method is the last one - we only return error codes, controls
	   to the client and send a response on the last method */

	final_method = (method2 == PAMPT_MAP_METHOD_NONE);
	rc = do_one_pam_auth(pb, method1, final_method, pam_service.str, pam_id_attr.str, 
			     pam_service_attr.str, fallback, pw_response_requested);
	if ((rc != LDAP_SUCCESS) && !final_method) {
		final_method = (method3 == PAMPT_MAP_METHOD_NONE);
		rc = do_one_pam_auth(pb, method2, final_method, pam_service.str, pam_id_attr.str,
				     pam_service_attr.str, fallback, pw_response_requested);
		if ((rc != LDAP_SUCCESS) && !final_method) {
			final_method = PR_TRUE;
			rc = do_one_pam_auth(pb, method3, final_method, pam_service.str, 
					     pam_id_attr.str, pam_service_attr.str, fallback,
					     pw_response_requested);
		}
	}

	delete_my_str_buf(&pam_id_attr);
	delete_my_str_buf(&pam_service);
	delete_my_str_buf(&pam_service_attr);

	return rc;
}
