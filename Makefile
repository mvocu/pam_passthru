#
# BEGIN COPYRIGHT BLOCK
# This Program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; version 2 of the License.
# 
# This Program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public License along with
# this Program; if not, write to the Free Software Foundation, Inc., 59 Temple
# Place, Suite 330, Boston, MA 02111-1307 USA.
# 
# In addition, as a special exception, Red Hat, Inc. gives You the additional
# right to link the code of this Program with code not covered under the GNU
# General Public License ("Non-GPL Code") and to distribute linked combinations
# including the two, subject to the limitations in this paragraph. Non-GPL Code
# permitted under this exception must only link to the code of this Program
# through those well defined interfaces identified in the file named EXCEPTION
# found in the source code files (the "Approved Interfaces"). The files of
# Non-GPL Code may instantiate templates or use macros or inline functions from
# the Approved Interfaces without causing the resulting work to be covered by
# the GNU General Public License. Only Red Hat, Inc. may make changes or
# additions to the list of Approved Interfaces. You must obey the GNU General
# Public License in all respects for all of the Program code and other code used
# in conjunction with the Program except the Non-GPL Code covered by this
# exception. If you modify this file, you may extend this exception to your
# version of the file, but you are not obligated to do so. If you do not wish to
# provide this exception without modification, you must delete this exception
# statement from your version and license this file solely under the GPL without
# exception. 
# 
# 
# Copyright (C) 2005 Red Hat, Inc.
# All rights reserved.
# END COPYRIGHT BLOCK
#
#
# GNU Makefile for Directory Server "PAM Pass Through Authentication" plugin
#
#

CC=gcc
LD=ld

389DS_VERSION = 1.3.5.17
389DS_SOURCE_BASE = /usr/local/src

INCLUDES_DIRSRV = $(shell pkg-config --cflags dirsrv)
LIBS_DIRSRV = $(shell pkg-config --libs dirsrv)
INCLUDES_NSPR = $(shell pkg-config --cflags nspr)
LIBS_NSPR = $(shell pkg-config --libs nspr)
INCLUDES_NSS = $(shell pkg-config --cflags nss)
LIBS_NSS = $(shell pkg-config --libs nss)
INCLUDES_389 = -I$(389DS_SOURCE_BASE)/389-ds-base-$(389DS_VERSION)/ldap/servers/slapd -I$(389DS_SOURCE_BASE)/389-ds-base-$(389DS_VERSION)/ldap/include

INCLUDES = $(INCLUDES_DIRSRV) $(INCLUDES_NSPR) $(INCLUDES_NSS) $(INCLUDES_389) -I.

CFLAGS= $(INCLUDES) -g -D_REENTRANT -fPIC -DHAVE_INTTYPES_H
LDFLAGS=
LIBS=$(LIBS_DIRSRV) $(LIBS_NSPR) $(LIBS_NSS)

OBJS=pam_ptimpl.o pam_ptconfig.o pam_ptdebug.o pam_ptpreop.o pam_ptpwmgmt.o
LOBJS=$(OBJS:.o=.lo)

EXTRALIBS += -lpam

all:	libpam-passthru-plugin.so

libpam-passthru-plugin.so: $(OBJS) 
	$(LD) -shared $(LDFLAGS) $(LIBS) $(EXTRALIBS) -o $@ $(OBJS)

.c.o:
	$(CC) $(CFLAGS) -c $<

veryclean: clean

clean:
	$(RM) $(OBJS)

#
# header file dependencies (incomplete)
#
$(OBJS):	pam_passthru.h
