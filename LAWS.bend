# Accepted contract root. The EXL3 greedy speculative acceptance laws bind the
# scalar leaf executed by the serving path (bend/exl3_accept.bend, emitted via
# bend/EXL3_ACCEPT.bend) to its independent list reference
# (bend/exl3_accept_spec.bend). Compiler, C glue, ctypes ABI and machine
# arithmetic retain the explicit boundaries stated in those modules.
import Base
import ./bend/exl3_accept_laws.bend as Exl3AcceptLaws
