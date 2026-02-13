#!/usr/bin/env python3
"""
Create stratified train/validation split for MPTP2078.
Ensures balanced domain distribution in both sets.
"""

import os
import json
import random
from collections import defaultdict
from pathlib import Path

def extract_domain(filename):
    """Extract domain from problem filename (e.g., relat_1__t3_relat_1.p -> relat_1)."""
    return filename.split('__')[0]

def create_stratified_split(problem_dir, train_ratio=0.8, seed=42):
    """
    Create stratified train/validation split.

    Args:
        problem_dir: Directory containing .p files
        train_ratio: Fraction for training (default 0.8)
        seed: Random seed for reproducibility

    Returns:
        dict with train_files, val_files, stats
    """
    random.seed(seed)

    # Group problems by domain
    domain_problems = defaultdict(list)
    all_problems = sorted([f for f in os.listdir(problem_dir) if f.endswith('.p')])

    for problem in all_problems:
        domain = extract_domain(problem)
        domain_problems[domain].append(problem)

    # Split each domain
    train_files = []
    val_files = []
    domain_stats = {}

    for domain, problems in sorted(domain_problems.items()):
        # Shuffle within domain
        shuffled = problems.copy()
        random.shuffle(shuffled)

        # Split
        n_train = int(len(problems) * train_ratio)
        train_domain = shuffled[:n_train]
        val_domain = shuffled[n_train:]

        train_files.extend(train_domain)
        val_files.extend(val_domain)

        domain_stats[domain] = {
            'total': len(problems),
            'train': len(train_domain),
            'val': len(val_domain)
        }

    return {
        'train_files': sorted(train_files),
        'val_files': sorted(val_files),
        'domain_stats': domain_stats,
        'total_train': len(train_files),
        'total_val': len(val_files),
        'seed': seed,
        'train_ratio': train_ratio
    }

def save_split(split_data, output_path):
    """Save split to JSON file."""
    with open(output_path, 'w') as f:
        json.dump(split_data, f, indent=2)

    print(f"Split saved to: {output_path}")
    print(f"  Training: {split_data['total_train']} problems")
    print(f"  Validation: {split_data['total_val']} problems")
    print(f"  Domains: {len(split_data['domain_stats'])}")

def print_split_summary(split_data):
    """Print summary statistics."""
    print("\n" + "="*70)
    print("STRATIFIED SPLIT SUMMARY")
    print("="*70)
    print(f"Total problems: {split_data['total_train'] + split_data['total_val']}")
    print(f"Training: {split_data['total_train']} ({split_data['train_ratio']*100:.0f}%)")
    print(f"Validation: {split_data['total_val']} ({(1-split_data['train_ratio'])*100:.0f}%)")
    print(f"Random seed: {split_data['seed']}")
    print(f"Domains: {len(split_data['domain_stats'])}")
    print("\nTop 10 domains by size:")
    print(f"{'Domain':<20} {'Total':<10} {'Train':<10} {'Val':<10}")
    print("-"*70)

    sorted_domains = sorted(
        split_data['domain_stats'].items(),
        key=lambda x: x[1]['total'],
        reverse=True
    )

    for domain, stats in sorted_domains[:10]:
        print(f"{domain:<20} {stats['total']:<10} {stats['train']:<10} {stats['val']:<10}")

    print("="*70)

def main():
    import sys

    if len(sys.argv) < 3:
        print("Usage: 01_create_split.py <problem_dir> <output_json> [train_ratio] [seed]")
        print("  Example: 01_create_split.py datasets/mptp2078/bushy splits/split_80_20_seed42.json 0.8 42")
        sys.exit(1)

    problem_dir = sys.argv[1]
    output_path = sys.argv[2]
    train_ratio = float(sys.argv[3]) if len(sys.argv) > 3 else 0.8
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 42

    # Create output directory
    os.makedirs(os.path.dirname(output_path), exist_ok=True)

    # Generate split
    print(f"Creating stratified split from: {problem_dir}")
    print(f"Train ratio: {train_ratio} | Seed: {seed}")

    split_data = create_stratified_split(problem_dir, train_ratio, seed)

    # Save and summarize
    save_split(split_data, output_path)
    print_split_summary(split_data)

    # Save train/val lists for easy use
    base_path = os.path.dirname(output_path)
    train_list = os.path.join(base_path, 'train.list')
    val_list = os.path.join(base_path, 'val.list')

    with open(train_list, 'w') as f:
        for fname in split_data['train_files']:
            f.write(f"bushy/{fname}\n")

    with open(val_list, 'w') as f:
        for fname in split_data['val_files']:
            f.write(f"bushy/{fname}\n")

    print(f"\nLists saved:")
    print(f"  {train_list}")
    print(f"  {val_list}")

if __name__ == '__main__':
    main()
