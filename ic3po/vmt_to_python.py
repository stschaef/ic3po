from vmt_parser import *

class ProtocolInstance:
    class Node:
        def __init__(self, variables, default_values):
            self.state = {var : default_values[var] for var in variables}

    def __init__(self, size, transition_relation, default_values):
        self.nodes = [Node(variables, default_values) for _ in range(size)]
        self.actions = get_actions(transition_relation)
        self.visited = [False for node in self.nodes]
        

    def get_actions(self, transition_relation):
        return None
    
    def reach_states(self)

        

def main():
    common.initialize()
    known, common.gopts = getopts("")
    args = sys.argv
    if len(args) != 2:
        print("Usage %s <file.smt2>" % args[0])
        exit(1)
    fname = args[1]
    ts_parser = TransitionSystem()
    with open(fname, 'r') as script:
        ts_parser.read_ts(script)

    orig = ts_parser.orig
    # print(orig._trel)
    # print(orig._nex2pre.keys())



    

if __name__ == "__main__":
    main()