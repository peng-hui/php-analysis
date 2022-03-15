#!/bin/bash - 
#===============================================================================
#
#          FILE: runkill.sh
# 
#         USAGE: ./runkill.sh 
# 
#   DESCRIPTION: 
# 
#       OPTIONS: ---
#  REQUIREMENTS: ---
#          BUGS: ---
#         NOTES: ---
#        AUTHOR: Penghui Li (Penghui), 
#  ORGANIZATION: 
#       CREATED: 09/26/19 00:57:11
#      REVISION:  ---
#===============================================================================

set -o nounset                              # Treat unset variables as an error
while :
do
  ./killprocess.pl
  echo "finished on round of killprocess"
  echo "sleep for 30 seconds"
  sleep 30
done

