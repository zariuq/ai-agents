#!/usr/bin/env python3
"""
Create Extended MPTP 5k dataset with chainy problems.

Chainy = for theorem tN, include t1...t(N-1) as axioms (chronological chain).
"""

import os
import re
import random
from pathlib import Path
from collections import defaultdict

# Config
PROBLEMS_DIR = Path("/home/zar/claude/atps/datasets/mml_8.1.15_fof/problems_small")
OUTPUT_DIR = Path("/home/zar/claude/atps/datasets/extended_mptp5k")
TRAIN_SIZE = 4200
VAL_SIZE = 800
TOTAL_SIZE = TRAIN_SIZE + VAL_SIZE
SEED = 42

# Extended MPTP articles (82 articles, ~5176 problems)
ARTICLES = """
compts_1 connsp_1 connsp_2 connsp_3
enumset1 filter_0 filter_1 filter_2 finset_1
funct_1 funct_2 funct_3 funct_4 funct_5 funct_6 funct_7 funct_8 funct_9
lattice2 lattice3 lattice4 lattice5 lattice6 lattice7 lattice8 lattices
mcart_1 orders_1 orders_2 orders_3 orders_4 orders_5
ordinal1 ordinal2 ordinal3 ordinal4 ordinal5 ordinal6 ordinal7
pre_topc relat_1 relat_2 relset_1 relset_2 relset_3 setfam_1 subset_1
tex_1 tex_2 tex_3 tex_4
tops_1 tops_2 tops_3 tops_4 tops_5
waybel_0 waybel_1 waybel_2 waybel_3 waybel_4 waybel_5 waybel_6 waybel_7 waybel_8 waybel_9
wellord1 wellord2 xboole_0 xboole_1
yellow_0 yellow_1 yellow_2 yellow_3 yellow_4 yellow_5 yellow_6 yellow_7 yellow_8 yellow_9 yellow19
zfmisc_1
""".split()

def parse_problem_name(filename):
    """Parse problem filename to extract article and theorem info.

    Examples:
        'abian__t5_abian' -> ('abian', 't', 5)
        'relat_1__l3_relat_1' -> ('relat_1', 'l', 3)
    """
    # Pattern: article__XN_article where X is theorem type (t, l, s, etc), N is number
    match = re.match(r'(.+)__([a-z])(\d+)_\1$', filename)
    if match:
        article, thm_type, thm_num = match.groups()
        return article, thm_type, int(thm_num)
    return None, None, None

def extract_conjecture(problem_file):
    """Extract the conjecture from a bushy problem file."""
    with open(problem_file) as f:
        for line in f:
            if line.strip().startswith('fof(') and 'conjecture' in line:
                return line.strip()
    return None

def conjecture_to_axiom(conj_line, prior_name):
    """Convert a conjecture line to an axiom line."""
    # Replace 'conjecture' with 'axiom' and update the name
    axiom_line = conj_line.replace(', conjecture,', ', axiom,')
    # Replace the original name with prior_name
    axiom_line = re.sub(r'^fof\([^,]+,', f'fof({prior_name},', axiom_line)
    return axiom_line

def create_chainy_problem(bushy_file, prior_problems):
    """Create chainy version by adding prior theorems as axioms.

    Args:
        bushy_file: Path to bushy problem file
        prior_problems: List of (name, file_path) for prior theorems in same article

    Returns:
        String content of chainy problem
    """
    # Read bushy problem
    with open(bushy_file) as f:
        bushy_content = f.read()

    # Extract prior theorem axioms
    prior_axioms = []
    for prior_name, prior_file in prior_problems:
        conj = extract_conjecture(prior_file)
        if conj:
            axiom = conjecture_to_axiom(conj, f'prior_{prior_name}')
            prior_axioms.append(axiom)

    if not prior_axioms:
        # No prior theorems, just return bushy
        return bushy_content

    # Insert prior axioms after the conjecture
    lines = bushy_content.split('\n')
    result = []
    conjecture_found = False

    for line in lines:
        result.append(line)
        if not conjecture_found and 'conjecture' in line and line.strip().startswith('fof('):
            # Insert prior axioms after conjecture
            result.extend(prior_axioms)
            conjecture_found = True

    return '\n'.join(result)

def main():
    random.seed(SEED)

    # 1. Collect all problems with ordering
    print("Collecting problems from 82 Extended MPTP articles...")
    article_problems = defaultdict(list)  # article -> [(name, path, type, num)]

    for article in ARTICLES:
        art_dir = PROBLEMS_DIR / article
        if not art_dir.exists():
            print(f"Warning: {article} not found")
            continue

        for prob_file in art_dir.iterdir():
            if prob_file.is_file():
                art, thm_type, thm_num = parse_problem_name(prob_file.name)
                if art:
                    article_problems[art].append((
                        prob_file.name,
                        prob_file,
                        thm_type,
                        thm_num
                    ))

    # 2. Sort problems within each article by (type, number)
    for article in article_problems:
        article_problems[article].sort(key=lambda x: (x[2], x[3]))

    # 3. Collect all problem paths
    all_problems = []
    for article in ARTICLES:
        if article in article_problems:
            for name, path, _, _ in article_problems[article]:
                all_problems.append((article, name, path))

    print(f"Total problems: {len(all_problems)}")

    # 4. Sample and split
    if len(all_problems) > TOTAL_SIZE:
        sampled = random.sample(all_problems, TOTAL_SIZE)
    else:
        sampled = all_problems
        print(f"Warning: Only {len(all_problems)} problems (wanted {TOTAL_SIZE})")

    random.shuffle(sampled)
    train_problems = sampled[:TRAIN_SIZE]
    val_problems = sampled[TRAIN_SIZE:]

    print(f"\nSplit:")
    print(f"  Train: {len(train_problems)}")
    print(f"  Val: {len(val_problems)}")

    # 5. Create chainy problems
    print("\nCreating chainy problems...")

    for split_name, problems in [('train', train_problems), ('val', val_problems)]:
        split_dir = OUTPUT_DIR / 'chainy' / split_name
        split_dir.mkdir(parents=True, exist_ok=True)

        for i, (article, name, bushy_path) in enumerate(problems):
            if (i + 1) % 500 == 0:
                print(f"  {split_name}: {i+1}/{len(problems)}")

            # Find prior problems in same article
            _, _, thm_type, thm_num = next(
                (x for x in article_problems[article] if x[0] == name),
                (None, None, None, None)
            )

            prior_probs = []
            if thm_type and thm_num:
                for prior_name, prior_path, prior_type, prior_num in article_problems[article]:
                    # Include if same type and lower number, or earlier type
                    if (prior_type == thm_type and prior_num < thm_num) or \
                       (prior_type < thm_type):
                        prior_probs.append((prior_name, prior_path))

            # Create chainy content
            chainy_content = create_chainy_problem(bushy_path, prior_probs)

            # Save
            output_file = split_dir / f"{article}__{name}"
            with open(output_file, 'w') as f:
                f.write(chainy_content)

    # 6. Save metadata
    meta_dir = OUTPUT_DIR / 'splits'
    meta_dir.mkdir(parents=True, exist_ok=True)

    with open(meta_dir / 'train.list', 'w') as f:
        for article, name, _ in train_problems:
            f.write(f"chainy/train/{article}__{name}\n")

    with open(meta_dir / 'val.list', 'w') as f:
        for article, name, _ in val_problems:
            f.write(f"chainy/val/{article}__{name}\n")

    with open(meta_dir / 'config.txt', 'w') as f:
        f.write(f"Dataset: Extended MPTP 5k (chainy)\n")
        f.write(f"Articles: {len(ARTICLES)} (Extended MPTP domains)\n")
        f.write(f"Total problems: {len(sampled)}\n")
        f.write(f"Train: {len(train_problems)}\n")
        f.write(f"Val: {len(val_problems)}\n")
        f.write(f"Seed: {SEED}\n")
        f.write(f"Format: Chainy (prior theorems as axioms)\n")

    print(f"\n✓ Dataset created: {OUTPUT_DIR}")
    print(f"  Chainy problems: chainy/train/ and chainy/val/")
    print(f"  Split files: splits/train.list and splits/val.list")

if __name__ == '__main__':
    main()
