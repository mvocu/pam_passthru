#include "pam_passthru.h"

/* need_new_pw() is called when non rootdn bind operation succeeds with authentication */ 
static int
_pam_need_new_pw( Slapi_PBlock *pb, long *t, Slapi_Entry *e, int pwresponse_req )
{
	time_t 		cur_time, pw_exp_date;
	Slapi_Mods smods;
	double		diff_t = 0;
	char 		*cur_time_str = NULL;
	char *passwordExpirationTime = NULL;
	char *timestring;
	char *dn;
	const Slapi_DN *sdn;
	passwdPolicy *pwpolicy = NULL;
	int	pwdGraceUserTime = 0;
	char graceUserTime[8];

	if (NULL == e) {
		return (-1);
	}
	slapi_mods_init (&smods, 0);
	sdn = slapi_entry_get_sdn_const( e );
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
                if (pwpolicy->pw_exp == 1) {
                        pw_exp_date = time_plus_sec(cur_time, pwpolicy->pw_maxage);

                        timestring = format_genTime (pw_exp_date);
                        slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpirationTime", timestring);
                        slapi_ch_free_string(&timestring);
                        slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpWarned", "0");
                        
                        pw_apply_mods(sdn, &smods);
                } else if (pwpolicy->pw_lockout == 1) {
                        pw_apply_mods(sdn, &smods);
                }
                slapi_mods_done(&smods);
                return ( 0 );
        }

        pw_exp_date = parse_genTime(passwordExpirationTime);

        slapi_ch_free_string(&passwordExpirationTime);

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
                slapi_ch_free_string(&timestring);
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
                pw_apply_mods(sdn, &smods);
                slapi_mods_done(&smods);
                return ( 0 );
        }

        /* check if password expired.  If so, abort bind. */
        cur_time_str = format_genTime ( cur_time );
        if ((pw_exp_date != NO_TIME) && (pw_exp_date != NOT_FIRST_TIME) &&
            (diff_t = difftime(pw_exp_date, parse_genTime(cur_time_str))) <= 0) {
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
                        pw_apply_mods(sdn, &smods);
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
                        disconnect_server( pb->pb_conn, pb->pb_op->o_connid,
                                pb->pb_op->o_opid, SLAPD_DISCONNECT_UNBIND, 0);
                }
                /* Apply current modifications */
                pw_apply_mods(sdn, &smods);
                slapi_mods_done(&smods);
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
                
                pw_exp_warned = slapi_entry_attr_get_int( e, "passwordExpWarned");
                if ( !pw_exp_warned ){
                        /* first time send out a warning */
                        /* reset the expiration time to current + warning time 
                         * and set passwordExpWarned to true
                         */
                        if (pb->pb_conn->c_needpw != 1) {
                                pw_exp_date = time_plus_sec(cur_time, pwpolicy->pw_warning);
                        }
                        
                        timestring = format_genTime(pw_exp_date);
                        slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpirationTime", timestring);
                        slapi_ch_free_string(&timestring);

                        slapi_mods_add_string(&smods, LDAP_MOD_REPLACE, "passwordExpWarned", "1");
                        
                        *t = pwpolicy->pw_warning;

                } else {
                        *t = (long)diff_t; /* jcm: had to cast double to long */
                }

                pw_apply_mods(sdn, &smods);
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
                return (2);
        } else {
                if (pwresponse_req && pwpolicy->pw_send_expiring) {
                        slapi_pwpolicy_make_response_control( pb, diff_t, -1, -1);
                        slapi_add_pwd_control(pb, LDAP_CONTROL_PWEXPIRING, diff_t);
                }
        }

        pw_apply_mods(sdn, &smods);
        slapi_mods_done(&smods);
        /* Leftover from "changeafterreset" condition */
        if (pb->pb_conn->c_needpw == 1) {
                slapi_add_pwd_control ( pb, LDAP_CONTROL_PWEXPIRED, 0);
        }
        /* passes checking, return 0 */
        return( 0 );
}
