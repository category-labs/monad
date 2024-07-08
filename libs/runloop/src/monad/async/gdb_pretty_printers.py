import gdb

class monad_async_context_printer(gdb.ValuePrinter):
    r"""Default printer:

    print *context
$2 = {
    is_running = false, is_suspended = false, switcher = 0x55555594eca0 <context_switcher_none_instance>, prev = 0x5060001da7a0, next = 0x5060001da860, sanitizer = {fake_stack_save = 0x0, bottom = 0x0, size = 0}}
    """
    def __init__(self, val):
        self.__val = val

    def display_hint(self):
        return 'monad_async_context'

    def to_string(self):
        ret = f"is_running = {str(self.__val['is_running'])}, is_suspended = {str(self.__val['is_suspended'])}, switcher = {self.__val['switcher']}"
        try:
            ret += f", stack_bottom = {str(self.__val['stack_bottom'])}, stack_top = {str(self.__val['stack_top'])}, stack_current = {str(self.__val['stack_current'])}"
        except:
            pass
        return ret

class monad_async_context_switcher_printer(gdb.ValuePrinter):
    r"""Default printer:

    print *switcher
$2 = {user_ptr = 0x0, contexts = std::atomic<unsigned int> = { 10000 }, contexts_list = {lock = {__size = '\000' <repeats 17 times>, "\002", '\000' <repeats 21 times>, __align = 0}, front = 0x5060001d5ee0, back = 0x5060002c14a0, 
    count = 10000}, self_destroy = 0x55555575f338 <monad_async_context_switcher_none_destroy>, create = 0x55555575f4f8 <monad_async_context_none_create>, destroy = 0x55555575f758 <monad_async_context_none_destroy>, 
  suspend_and_call_resume = 0x55555575f7a8 <monad_async_context_none_suspend_and_call_resume>, resume = 0x55555575f848 <monad_async_context_none_resume>, resume_many = 0x55555575fde8 <monad_async_context_none_resume_many>}
    """
    def __init__(self, val):
        self.__val = val

    def display_hint(self):
        return 'monad_async_context_switcher'

    def to_string(self):
        return f"user_ptr = {str(self.__val['user_ptr'])}, contexts = {str(self.__val['contexts'])}"

    def children(self):
        try:
            self.__val['contexts_list']
        except:
            return None
        next = self.__val['contexts_list']['front']
        idx = 0
        while next:
            yield (str(idx), next.dereference())
            next = next['next']
            idx += 1

def build_pretty_printer():
    pp = gdb.printing.RegexpCollectionPrettyPrinter("monad_async_c")
    pp.add_printer('monad_async_context', '^monad_async_context_head$', monad_async_context_printer)
    pp.add_printer('monad_async_context_switcher', '^monad_async_context_switcher_head$', monad_async_context_switcher_printer)
    return pp

gdb.printing.register_pretty_printer(gdb.current_objfile(), build_pretty_printer())
