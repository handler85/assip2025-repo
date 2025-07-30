import matplotlib.pyplot as plt
import seaborn as sns
import numpy as np

plt.style.use('default') 
sns.set_palette("husl")

modern_colors = [
    '#2E8B57',  
    '#FF6B6B', 
    '#4ECDC4',  
    '#45B7D1', 
    '#96CEB4',
    '#FFEAA7' 
]

plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['SF Pro Display', 'Segoe UI', 'Roboto', 'Arial', 'DejaVu Sans'],
    'font.size': 11,
    'axes.titlesize': 16,
    'axes.titleweight': '600',
    'axes.labelsize': 12,
    'axes.labelweight': '500',
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'figure.titlesize': 18,
    'axes.spines.top': False,
    'axes.spines.right': False,
    'axes.spines.left': True,
    'axes.spines.bottom': True,
    'axes.linewidth': 0.8,
    'grid.alpha': 0.3,
    'grid.linewidth': 0.5
})

labels = ["NE", "M", "IP", "U", "T", "S"]
full_labels = ["No Errors", "Mathematical\nError", "Incorrect Formal\nProof Strategy", 
               "Tactic\nFailure", "Inefficient\nStrategy", "Syntax\nError"]
counts = [120, 59, 32, 25, 6, 2]
l_suberror = 46
m_main = counts[1] - l_suberror

fig, ax = plt.subplots(figsize=(12, 8))
fig.patch.set_facecolor('white')

bars = []
for i, (label, count) in enumerate(zip(labels, counts)):
    color = modern_colors[i]
    
    if label == "M":
        bar1 = ax.bar(i, m_main, width=0.7, color=color, 
                     edgecolor='white', linewidth=2, alpha=0.9)
        l_color = '#FF8E8E'
        bar2 = ax.bar(i, l_suberror, bottom=m_main, width=0.7, 
                     color=l_color, edgecolor='white', linewidth=2, 
                     alpha=0.8, hatch='///')
        bars.extend([bar1, bar2])
        
        ax.text(i, m_main/2, f'{m_main}', ha='center', va='center', 
               color='white', fontsize=11, fontweight='bold')
        ax.text(i, m_main + l_suberror/2, f'{l_suberror}', ha='center', va='center', 
               color='white', fontsize=11, fontweight='bold')
    else:
        bar = ax.bar(i, count, width=0.7, color=color, 
                    edgecolor='white', linewidth=2, alpha=0.9)
        bars.append(bar)
        
        ax.text(i, count + 2, f'{count}', ha='center', va='bottom', 
               fontsize=11, fontweight='600', color='#2C3E50')

ax.set_title('Primary Error Distribution\nDeepSeek-Prover-V2-7B on MiniF2F-test (Pass@1)', 
            pad=25, fontsize=16, fontweight='600', color='#2C3E50', 
            linespacing=1.3)

ax.set_xlabel('Error Categories', fontsize=12, fontweight='500', color='#34495E', labelpad=15)
ax.set_ylabel('Frequency Count', fontsize=12, fontweight='500', color='#34495E', labelpad=15)

ax.grid(axis='y', alpha=0.3, linestyle='-', linewidth=0.5, color='#BDC3C7')
ax.set_axisbelow(True)

ax.spines['top'].set_visible(False)
ax.spines['right'].set_visible(False)
ax.spines['left'].set_color('#BDC3C7')
ax.spines['bottom'].set_color('#BDC3C7')

ax.tick_params(axis='both', colors='#7F8C8D', length=4, width=0.8)
ax.set_xticks(range(len(labels)))
ax.set_xticklabels(full_labels, fontsize=10, color='#2C3E50')

ax.set_ylim(0, max(counts) * 1.15)

from matplotlib.patches import Patch
legend_elements = [
    Patch(facecolor='#FF8E8E', edgecolor='white', linewidth=2, 
          alpha=0.8, hatch='///', label='L: Repetitive Loop/Generation Failure')
]

legend = ax.legend(handles=legend_elements, loc='upper right', 
                   frameon=True, fancybox=True, shadow=True, 
                   framealpha=0.95, edgecolor='#BDC3C7', 
                   title='Sub-error', title_fontsize=11, 
                   fontsize=10, bbox_to_anchor=(0.98, 0.98))
legend.get_frame().set_facecolor('white')
legend.get_title().set_color('#2C3E50')
legend.get_title().set_fontweight('600')

ax.set_facecolor('#FAFBFC')

plt.tight_layout()

for spine in ax.spines.values():
    spine.set_linewidth(0.8)

# plt.savefig("deepseek_error_dist.pdf", bbox_inches="tight", facecolor='white', edgecolor='none', dpi=300)
plt.savefig("deepseek_error_dist.png", bbox_inches="tight", facecolor='white', edgecolor='none', dpi=300)

plt.show()