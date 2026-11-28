"""Draw the finite set of candidates left after the two elementary constructions."""
import csv
from pathlib import Path
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter

folder = Path(__file__).resolve().parent
with (folder / "witnesses.csv").open() as stream:
    earlier = [int(row["e"]) for row in csv.DictReader(stream)]
endpoint = 435643
fig, ax = plt.subplots(figsize=(6.65, 1.45), layout="constrained")
ax.vlines(earlier, 0.04, 0.38, color="#115a63", lw=1)
ax.plot(endpoint, 0.21, "D", color="#ad4026", ms=5)
ax.text(97000, .60, "109 earlier endpoints admit five factorials", fontsize=9, color="#115a63")
ax.annotate("435643", xy=(endpoint, .21), xytext=(endpoint, .70),
            ha="right", color="#ad4026", fontsize=9,
            arrowprops={"arrowstyle": "-", "color": "#ad4026", "lw": .8})
ax.set(xlim=(90000, 445000), ylim=(-.02, 1.05), yticks=[], xlabel="Largest factorial index")
ax.xaxis.set_major_formatter(FuncFormatter(lambda x, _: f"{x:,.0f}"))
ax.spines[["top", "right", "left"]].set_visible(False)
ax.tick_params(axis="x", labelsize=8)
fig.savefig(folder / "endpoints.pdf", metadata={"CreationDate": None, "ModDate": None})
