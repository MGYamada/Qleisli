#!/bin/sh
# Copyright 2026 Masahiko G. Yamada. SPDX-License-Identifier: Apache-2.0
# Immutable descendant/pipe test; private state lives beside its invocation link.
case "${0##*/}" in
    exit|wait)
        sleep 30 &
        echo $! > "${0%/*}/pid"
        if [ "${0##*/}" = wait ]; then wait; fi ;;
    ok)
        cat >/dev/null
        printf 'ok\n' ;;
    *) exit 2 ;;
esac
