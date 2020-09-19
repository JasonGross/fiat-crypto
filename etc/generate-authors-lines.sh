#!/usr/bin/env bash

echo 'Require Import Coq.Strings.String Coq.Lists.List.'
echo 'Import ListNotations.'
echo 'Local Open Scope string_scope.'
echo 'Local Open Scope list_scope.'
echo 'Definition AuthorsLines := ['
sed 's/"/""""/g; s/^\(.*\)$/"\1";/g' "$@"
echo '""].'
