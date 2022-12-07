#!/bin/bash

set -e
#set -x

SUCMD=""

if [ -t 0 ] ; then
    groupadd -g "${GROUP_ID}" "${GROUP}"
    useradd -u "${USER_ID}" -g "${GROUP_ID}" "${USER}" -d "${HOME_DIR}" -s /bin/bash
    chown -R "${USER}:${GROUP}" "${HOME_DIR}"
    SUCMD="su -P ${USER} -c"
fi

${SUCMD} "${@}"
