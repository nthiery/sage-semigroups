import sys
import logging
from recursive_monkey_patch import monkey_patch

import sage
sage_semigroups = sys.modules[__name__]
import sage_semigroups.monoids
monkey_patch(sage_semigroups.monoids, sage.monoids, log_level=logging.INFO)
