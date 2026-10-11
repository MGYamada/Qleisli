#!/usr/bin/env python3
"""Transparent, bounded-study native invocation recorder; no acceptance logic."""
import json, os, sys
with open(os.environ['QLEISLI_STUDY_NATIVE_LOG'], 'a', encoding='utf-8') as stream:
    stream.write(json.dumps(sys.argv[1:])+'\n')
os.execv(os.environ['QLEISLI_STUDY_NATIVE'], [os.environ['QLEISLI_STUDY_NATIVE'], *sys.argv[1:]])
