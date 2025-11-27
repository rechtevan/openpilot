#!/usr/bin/env python3
"""
Visualization for formal model validation results.

Generates:
1. State transition diagrams (graphviz)
2. Coverage heatmaps
3. Divergence traces
4. Exploration statistics

All outputs go to .local/validation_results/ (gitignored)
"""

import json
import os
from pathlib import Path
from datetime import datetime
from collections import defaultdict
from typing import Dict, List, Optional

try:
    import matplotlib
    matplotlib.use('Agg')  # Non-interactive backend
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    MATPLOTLIB_AVAILABLE = False

try:
    import graphviz
    GRAPHVIZ_AVAILABLE = True
except ImportError:
    GRAPHVIZ_AVAILABLE = False

import numpy as np

from env_state_machine import StateMachineReference, State, EventType, Events

# Output directory
OUTPUT_DIR = Path(__file__).parent.parent.parent / ".local" / "validation_results" / "visualizations"


def ensure_output_dir():
    """Create output directory if it doesn't exist"""
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    return OUTPUT_DIR


class StateTransitionVisualizer:
    """Visualize state machine transitions"""

    def __init__(self):
        self.transitions = defaultdict(lambda: defaultdict(int))
        self.state_visits = defaultdict(int)

    def record_transition(self, from_state: State, to_state: State, events: set):
        """Record a state transition"""
        self.transitions[from_state][to_state] += 1
        self.state_visits[from_state] += 1
        self.state_visits[to_state] += 1

    def explore_state_space(self, num_traces: int = 1000, trace_length: int = 100,
                            seed: Optional[int] = None):
        """Explore state space and record transitions"""
        rng = np.random.default_rng(seed)

        for _ in range(num_traces):
            machine = StateMachineReference()

            for _ in range(trace_length):
                prev_state = machine.state

                # Random events
                events_bitmap = rng.integers(0, 2, size=9)
                event_set = {EventType(i) for i, v in enumerate(events_bitmap) if v}
                events = Events(events=event_set)

                new_state = machine.step(events)
                self.record_transition(prev_state, new_state, event_set)

    def generate_graphviz(self, filename: str = "state_machine") -> Optional[str]:
        """Generate state transition diagram using graphviz"""
        if not GRAPHVIZ_AVAILABLE:
            print("Note: graphviz not available, skipping diagram generation")
            return None

        ensure_output_dir()

        dot = graphviz.Digraph(comment='State Machine Transitions')
        dot.attr(rankdir='LR', size='12,8')

        # Define colors for states
        state_colors = {
            State.DISABLED: '#ffcccc',      # Light red
            State.PRE_ENABLED: '#ffffcc',   # Light yellow
            State.ENABLED: '#ccffcc',       # Light green
            State.SOFT_DISABLING: '#ffccff', # Light magenta
            State.OVERRIDING: '#ccccff',    # Light blue
        }

        # Add nodes (states)
        max_visits = max(self.state_visits.values()) if self.state_visits else 1
        for state in State:
            visits = self.state_visits.get(state, 0)
            # Scale node size by visits
            width = 0.8 + (visits / max_visits) * 0.7
            dot.node(
                state.name,
                f"{state.name}\n({visits:,})",
                style='filled',
                fillcolor=state_colors.get(state, '#ffffff'),
                width=str(width),
                fontsize='10'
            )

        # Add edges (transitions)
        max_trans = max(
            count
            for from_trans in self.transitions.values()
            for count in from_trans.values()
        ) if self.transitions else 1

        for from_state, to_states in self.transitions.items():
            for to_state, count in to_states.items():
                # Scale edge width by transition count
                penwidth = 0.5 + (count / max_trans) * 3
                color = '#333333' if from_state != to_state else '#999999'
                dot.edge(
                    from_state.name,
                    to_state.name,
                    label=f'{count:,}',
                    penwidth=str(penwidth),
                    color=color,
                    fontsize='8'
                )

        # Render
        output_path = OUTPUT_DIR / filename
        dot.render(output_path, format='png', cleanup=True)
        dot.render(output_path, format='svg', cleanup=True)

        print(f"Generated: {output_path}.png and {output_path}.svg")
        return str(output_path)

    def generate_heatmap(self, filename: str = "transition_heatmap") -> Optional[str]:
        """Generate transition heatmap using matplotlib"""
        if not MATPLOTLIB_AVAILABLE:
            print("Note: matplotlib not available, skipping heatmap generation")
            return None

        ensure_output_dir()

        states = list(State)
        n_states = len(states)

        # Build transition matrix
        matrix = np.zeros((n_states, n_states))
        for i, from_state in enumerate(states):
            for j, to_state in enumerate(states):
                matrix[i, j] = self.transitions[from_state][to_state]

        # Normalize rows
        row_sums = matrix.sum(axis=1, keepdims=True)
        row_sums[row_sums == 0] = 1  # Avoid division by zero
        matrix_norm = matrix / row_sums

        # Create heatmap
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

        # Raw counts
        im1 = ax1.imshow(matrix, cmap='Blues')
        ax1.set_xticks(range(n_states))
        ax1.set_yticks(range(n_states))
        ax1.set_xticklabels([s.name for s in states], rotation=45, ha='right')
        ax1.set_yticklabels([s.name for s in states])
        ax1.set_xlabel('To State')
        ax1.set_ylabel('From State')
        ax1.set_title('Transition Counts')
        plt.colorbar(im1, ax=ax1, label='Count')

        # Add text annotations
        for i in range(n_states):
            for j in range(n_states):
                if matrix[i, j] > 0:
                    ax1.text(j, i, f'{int(matrix[i, j]):,}',
                             ha='center', va='center', fontsize=7)

        # Normalized probabilities
        im2 = ax2.imshow(matrix_norm, cmap='Greens', vmin=0, vmax=1)
        ax2.set_xticks(range(n_states))
        ax2.set_yticks(range(n_states))
        ax2.set_xticklabels([s.name for s in states], rotation=45, ha='right')
        ax2.set_yticklabels([s.name for s in states])
        ax2.set_xlabel('To State')
        ax2.set_ylabel('From State')
        ax2.set_title('Transition Probabilities')
        plt.colorbar(im2, ax=ax2, label='Probability')

        # Add text annotations
        for i in range(n_states):
            for j in range(n_states):
                if matrix_norm[i, j] > 0.01:
                    ax2.text(j, i, f'{matrix_norm[i, j]:.2f}',
                             ha='center', va='center', fontsize=7)

        plt.tight_layout()

        output_path = OUTPUT_DIR / f"{filename}.png"
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        plt.close()

        print(f"Generated: {output_path}")
        return str(output_path)


class ValidationResultsVisualizer:
    """Visualize validation results from JSON files"""

    def __init__(self, results_dir: Optional[Path] = None):
        self.results_dir = results_dir or (OUTPUT_DIR.parent)
        self.results = []

    def load_results(self):
        """Load all JSON result files"""
        self.results = []
        for json_file in self.results_dir.glob("*.json"):
            try:
                with open(json_file) as f:
                    data = json.load(f)
                    data['filename'] = json_file.name
                    self.results.append(data)
            except Exception as e:
                print(f"Error loading {json_file}: {e}")

        self.results.sort(key=lambda x: x.get('timestamp', ''))
        return self.results

    def generate_coverage_comparison(self, filename: str = "coverage_comparison") -> Optional[str]:
        """Generate coverage comparison chart"""
        if not MATPLOTLIB_AVAILABLE:
            print("Note: matplotlib not available, skipping coverage chart")
            return None

        if not self.results:
            self.load_results()

        if not self.results:
            print("No results to visualize")
            return None

        ensure_output_dir()

        fig, ax = plt.subplots(figsize=(12, 6))

        # Get all unique states across results
        all_states = set()
        for r in self.results:
            all_states.update(r.get('coverage', {}).keys())
        all_states = sorted(all_states)

        # Plot coverage for each result
        x = np.arange(len(all_states))
        width = 0.8 / len(self.results)

        for i, result in enumerate(self.results[-5:]):  # Last 5 results
            coverage = result.get('coverage', {})
            values = [coverage.get(s, 0) for s in all_states]
            label = f"{result.get('method', 'unknown')} ({result.get('timestamp', '')[:10]})"
            ax.bar(x + i * width, values, width, label=label)

        ax.set_xlabel('State')
        ax.set_ylabel('Visit Count')
        ax.set_title('Coverage Comparison Across Validation Runs')
        ax.set_xticks(x + width * len(self.results[-5:]) / 2)
        ax.set_xticklabels(all_states, rotation=45, ha='right')
        ax.legend()

        plt.tight_layout()

        output_path = OUTPUT_DIR / f"{filename}.png"
        plt.savefig(output_path, dpi=150, bbox_inches='tight')
        plt.close()

        print(f"Generated: {output_path}")
        return str(output_path)

    def generate_summary_report(self, filename: str = "validation_summary") -> str:
        """Generate HTML summary report"""
        if not self.results:
            self.load_results()

        ensure_output_dir()

        html = """<!DOCTYPE html>
<html>
<head>
    <title>Formal Model Validation Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; background: #f5f5f5; }
        h1 { color: #333; }
        .summary { background: white; padding: 20px; border-radius: 8px; margin: 10px 0; }
        table { border-collapse: collapse; width: 100%; }
        th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
        th { background: #4CAF50; color: white; }
        tr:nth-child(even) { background: #f2f2f2; }
        .success { color: green; }
        .failure { color: red; }
        .warning { color: orange; }
        img { max-width: 100%; margin: 10px 0; }
    </style>
</head>
<body>
    <h1>Formal Model Validation Report</h1>
    <p>Generated: """ + datetime.now().isoformat() + """</p>

    <div class="summary">
        <h2>Validation Results Summary</h2>
        <table>
            <tr>
                <th>Timestamp</th>
                <th>Model</th>
                <th>Method</th>
                <th>Traces</th>
                <th>Divergences</th>
                <th>Status</th>
            </tr>
"""
        for result in self.results[-10:]:  # Last 10 results
            divergences = result.get('divergences_found', 0)
            status_class = 'success' if divergences == 0 else 'failure'
            status_text = 'PASS' if divergences == 0 else 'DIVERGENCES FOUND'

            html += f"""
            <tr>
                <td>{result.get('timestamp', 'N/A')[:19]}</td>
                <td>{result.get('model_name', 'N/A')}</td>
                <td>{result.get('method', 'N/A')}</td>
                <td>{result.get('num_traces', 'N/A'):,}</td>
                <td class="{status_class}">{divergences}</td>
                <td class="{status_class}">{status_text}</td>
            </tr>
"""

        html += """
        </table>
    </div>

    <div class="summary">
        <h2>Visualizations</h2>
        <h3>State Machine Diagram</h3>
        <img src="visualizations/state_machine.svg" alt="State Machine" onerror="this.style.display='none'">

        <h3>Transition Heatmap</h3>
        <img src="visualizations/transition_heatmap.png" alt="Heatmap" onerror="this.style.display='none'">

        <h3>Coverage Comparison</h3>
        <img src="visualizations/coverage_comparison.png" alt="Coverage" onerror="this.style.display='none'">
    </div>
"""

        # Add divergence details if any
        divergence_results = [r for r in self.results if r.get('divergences_found', 0) > 0]
        if divergence_results:
            html += """
    <div class="summary">
        <h2>Divergence Details</h2>
"""
            for result in divergence_results[-3:]:
                html += f"<h3>{result.get('model_name')} - {result.get('method')}</h3>"
                html += "<ul>"
                for d in result.get('divergence_details', [])[:5]:
                    html += f"<li>Step {d.get('step')}: Events={d.get('events')}, "
                    html += f"Ref={d.get('ref_state')}, Impl={d.get('impl_state')}</li>"
                html += "</ul>"

            html += "</div>"

        html += """
</body>
</html>
"""

        output_path = OUTPUT_DIR.parent / f"{filename}.html"
        with open(output_path, 'w') as f:
            f.write(html)

        print(f"Generated: {output_path}")
        return str(output_path)


def generate_all_visualizations(num_traces: int = 5000, trace_length: int = 100):
    """Generate all visualizations"""
    print("=" * 60)
    print("Generating Visualizations")
    print("=" * 60)

    # State transition diagram and heatmap
    print("\n[1/4] Exploring state space...")
    vis = StateTransitionVisualizer()
    vis.explore_state_space(num_traces, trace_length)

    print("\n[2/4] Generating state transition diagram...")
    vis.generate_graphviz()

    print("\n[3/4] Generating transition heatmap...")
    vis.generate_heatmap()

    # Results visualizations
    print("\n[4/4] Generating validation results summary...")
    results_vis = ValidationResultsVisualizer()
    results_vis.load_results()
    results_vis.generate_coverage_comparison()
    results_vis.generate_summary_report()

    print("\n" + "=" * 60)
    print(f"Visualizations saved to: {OUTPUT_DIR}")
    print(f"Summary report: {OUTPUT_DIR.parent}/validation_summary.html")
    print("=" * 60)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Generate validation visualizations")
    parser.add_argument("--traces", type=int, default=5000, help="Number of exploration traces")
    parser.add_argument("--length", type=int, default=100, help="Trace length")

    args = parser.parse_args()

    generate_all_visualizations(args.traces, args.length)
