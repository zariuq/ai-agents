import random
import json
import sys
from pathlib import Path

class MegalodonFuzzer:
    def __init__(self, grammar_file):
        with open(grammar_file, 'r') as f:
            self.grammar = json.load(f)
        self.names = ["foo", "bar", "baz", "A", "B", "x", "y", "z", "P", "Q"]
        self.types = ["set", "prop", "set -> set", "set -> prop"]
        
    def gen_name(self):
        return random.choice(self.names) + str(random.randint(0, 100))
        
    def gen_type(self):
        return random.choice(self.types)
        
    def gen_term(self, depth=0):
        if depth > 3:
            return self.gen_name()
            
        choice = random.random()
        if choice < 0.4:
            return self.gen_name()
        elif choice < 0.7:
            # Application
            return f"({self.gen_term(depth+1)} {self.gen_term(depth+1)})"
        elif choice < 0.9:
            # Implication
            return f"({self.gen_term(depth+1)} -> {self.gen_term(depth+1)})"
        else:
            # Quantifier
            var = self.gen_name()
            return f"(forall {var}:{self.gen_type()}, {self.gen_term(depth+1)})"

    def gen_definition(self):
        name = self.gen_name()
        return f"Definition {name} : {self.gen_type()} := {self.gen_term()}."

    def gen_parameter(self):
        name = self.gen_name()
        return f"Parameter {name} : {self.gen_type()}."

    def gen_file(self, num_items=5):
        lines = []
        # lines.append("(* Generated Fuzz File *)") # Comments at start are invalid
        for _ in range(num_items):
            if random.random() < 0.5:
                lines.append(self.gen_definition())
            else:
                lines.append(self.gen_parameter())
        return "\n\n".join(lines)

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 gen_mg.py <output_dir> [count]")
        return
        
    out_dir = Path(sys.argv[1])
    out_dir.mkdir(parents=True, exist_ok=True)
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    
    fuzzer = MegalodonFuzzer('tools/grammar_snapshot.json')
    
    for i in range(count):
        fname = out_dir / f"fuzz_{i:03d}.mg"
        with open(fname, 'w') as f:
            f.write(fuzzer.gen_file())
    
    print(f"Generated {count} fuzz files in {out_dir}")

if __name__ == "__main__":
    main()
