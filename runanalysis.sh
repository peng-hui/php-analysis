#!/bin/bash - 
#===============================================================================
#
#          FILE: runconstructcfg.sh
# 
#         USAGE: ./runconstructcfg.sh 
# 
#   DESCRIPTION: 
# 
#       OPTIONS: ---
#  REQUIREMENTS: ---
#          BUGS: ---
#         NOTES: ---
#        AUTHOR: Penghui Li (Penghui), 
#  ORGANIZATION: 
#       CREATED: 08/27/19 21:57:02
#      REVISION:  ---
#===============================================================================

set -o nounset                              # Treat unset variables as an error
php main_analysis.php   /data/cpu_dos_data/phpapps/100/102/

