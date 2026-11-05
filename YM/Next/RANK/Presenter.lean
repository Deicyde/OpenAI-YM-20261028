import YM.Next.RANK.Incoming
import YM.Next.RANK.Pilgrim


/-!
# Conditional weak comparison factory

Inputs before the Maxwell comparison: specific short-stencil data on THIS history;
Heating together with W estimates in unmarked pushed density (and raw step);
aligned comparability on the step kernels only (not a normalized physical field
comparison axiom). Everything needs Actual producers. No use of asserted labels
on an independently shot period or orientation/mask transformation after retuning.
Orders include ALL modes up to `m` requested in previous files. Quote here charges
the 2 probes per rank row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Set Function Filter RG Lattice Wilson MeasureTheory Perch Peak Station Cells Common Beamer Prayer Glimmer Value Read Market Glyph Marker Exponential Camp
open scoped Classical Topology BigOperators

variable {G : Gauge} {C : Family G} {n m d k j N p : ℕ} {O : Schedule}
variable {x : Points n} (b : ℝ)

section
variable (X : AtlasData G C.S p) (V : Heater C k d) (c : Course C N p k) (Y : (u : ℕ) → Rep G (C.side u p))

-- expected initial Wick polynomial `V v`; reflected targets accounted in cell using same F.W. Note approximation tolerance here consumed ONLY inside W masks and requires a formal Gaussian computation on a Wind; not an estimate on true normalized moment. Also need true equality of Dust on all fields. No post-L fudge.

def asked (o : Fin n → C.label d) : Fin n → C.book.Token := fun i => ⟨d,o i⟩

def Cumulus (z : Fin n → Cover) (h : m≤ k) (q : Heater C k d) (v : Fin n → C.label d) (u : Chamber G C.S m p→ℝ) :=
    let P := fun i => q (v i)
    Exponential.connected (Answer X z h P (fun y => (u y:ℂ))) (phased X z h P _)
lemma cumulates (z : Fin n→Cover) (h : m ≤ k) (v : Fin n→ C.label d) (u : Chamber G C.S m p→ℝ) :
    Expands (Cumulus X z h V v u) (Answer X z h (fun i => V (v i)) (fun y => (u y:ℂ))) := Exponential.connected_spec _ (phased ..)

def Clipped (x : Points n) (v : Fin n→ C.label d) (hi : k ≤ N) (degree : ℕ) (D : Demand) (slot : ℕ) :=
    let A := C.path.levels
    let s := clim A k
    let l := middle A b k
    let L := Y l
    let h:= before A b k
    let T:= Ship.yard C b hi p
    let g := L.p
    let ψ := Peak.route A b k p D.Q g.B
    let t := Ship.clients C (asked v) b k N p x
    let f:= readers (b:=b) (C:=C) (p:=p) x hi (h.trans hi)
    ∀ g₀ : g.B=walls (clim A l), ∀ hs : Perch.Shelf D slot s (clim A l),
      ∃ (α β : Type), ∃ (_ : Fintype α) (_ : Fintype β), ∃ (H : α → SourceAt G f) (K : β → Lifted G f g.threshold)
        (W : T.Cell × flame (Fin n) → SourceAt G f),
        Dock.Reception (Peak.Meter A g₀ hs) H K ∧ Background L K ∧
          c.flow (Array.stamp T (C.beta N p) (Read.bareP t)) l (h.trans hi)=dust L (Sum.elim H W) K ∧
          (∀ i,(W i).fires=sectionAt i ∧ (W i).extent=ψ i.1) ∧
          ∀ i U, Healthy g.threshold (ψ i) U →
          ∃ u : Chamber G C.S l p → ℝ, Wind A u (fraction n degree s) ∧
            ∀ a : flame (Fin n), ‖(W (i,a)).value U-(Array.reorient T i (Cumulus X (Station.choose A b k x) h V v u)).part a.val‖ ≤ Perch.bill (-3/2) s

-- price after-test consumed upstream of uniform station. Includes projection of all queries.

variable (w : Fin n → C.label d) (degree : ℕ)

def Period (x : Points n) (k : ℕ) : Prop :=
    let A:=C.path.levels; let s:= clim A k
    passing w k degree b ∧ ∀ g : Fit A b k x,
      Prayer.Meridian d (Ship.fitting g) (G:=G) (fraction n degree s) (fraction n degree s) (bill (-3) s) (bill (fuel degree n) s)
        (bill (-2) s) (Station.mag A b k) (lengthW s) ∧
        ∀ q P F, Expands P q → Expands F (Read.maxProfile C (Station.tested A b k x) (joint w)) →
          (∀ z, ‖q.part z-(Read.maxProfile C (Station.tested A b k x) (joint w)).part z‖ ≤ bill (-3/2) s) →
            ‖P-F‖+bill (-3/2) s ≤ bill (-31/32) s

lemma pedalling (x : Points n) (h : G.Simple) (H : C.Makes) (hb : 0 < b) (hD : saves C d+3 ≤ b) (hx : x∈conf n) :
    ∀ᶠ k in atTop, Period b w degree x k := by
  let Y:= C.path.levels
  filter_upwards [passing_all h H degree w b hb hD,clockwise degree Y h hb x hx d, Glimmer.accumulate ℕ atTop _ (Read.maxProfile C x (joint w))
    (profile_tends _ _ (Maxwell.table_smooth C.labels) hx (Station.tuning Y x h hb)) Y.clock.hatBeta (Station.hat_rate Y h)] with k h1 h2 h3
  exact ⟨h1,fun hp => ⟨h2 hp,h3⟩⟩

lemma honor {T : Cells.Tiling (C.side N p)} (i : T.Cell) (a s : veil (Fin n)) (f : flame (Fin n)) :
    ‖(Array.reorient T i a).part f.val+(Peak.view T s (i,f))‖ ≤ ‖a-s‖ := by
  change _ ≤ ‖a.part-s.part‖
  apply le_trans _ ((pi_norm_le_iff_of_nonneg (norm_nonneg (a.part-s.part))).1 le_rfl f.val)
  unfold Peak.view Array.reorient
  split_ifs
  · rw [shade_part,shade_part, ← star_add,norm_star]; exact le_of_eq (congr_arg norm (sub_eq_add_neg (a.part f.val) (s.part f.val)).symm)
  exact le_of_eq (congr_arg norm (sub_eq_add_neg ..).symm)

lemma crushed (hp : Period b w degree x k) (g : Fit C.path.levels b k x) {T' : C.label d→ₗ[ℂ] C.label d} (hV : Heating C k N p d degree V T')
    (t : Fin n→C.label d) (hi : k≤N) (ht : ∀ i, Price.Solves C (Station.mag C.path.levels b k) d k N p T' (w i) (t i))
    (hb : Bell C.path.levels X d degree g) (D : Demand) (slot : ℕ) (h : Clipped b X V c Y x t hi degree D slot) :
    Arrangements hi c Y (joint w) (asked t) g D slot := by
  let A := C.path.levels; let T:= Ship.yard C b hi p; let S := clim A k
  let f:= Ship.targets C (joint w) g
  intro hv hs; obtain ⟨α,β,bα,bβ,H,K,W,h1,hbg,h2,h3,h4⟩ := h hv hs
  refine ⟨α,β,bα,bβ,H,K,W,h1,hbg,h2,fun i => ⟨(h3 i).1,(h3 i).2,fun U HH => ?_⟩⟩
  obtain ⟨y,hy,hh⟩ := h4 i.1 U HH
  obtain ⟨hc,hp⟩ := hp; obtain ⟨Q,L⟩ := hp g
  let u:= Station.choose A b k x
  let D' := Cumulus X u (before A b k) V t y
  have he : ‖D'-f‖+bill (-3/2) S ≤ bill (-31/32) S := L _ _ _ (cumulates X V u (before A b k) t y)
    (Read.cumulative C (Station.tested A b k x) (joint w) (Ship.fitting g)) (fun s => sizes w g degree hi hV hb y hy hc t ht Q s)
  let v:= (W i).value U; let z:= Peak.view T f i; let a:= (Array.reorient T i.1 D').part i.2.val
  change ‖v+z‖ ≤ _
  rw [show v+z=(a+z)+(v-a) by ring]; exact (norm_add_le ..).trans ((add_le_add (honor (C:=C) i.1 _ _ i.2) (hh _)).trans he)
end

variable {W : Table C.book} (A : HaarBudget G) (D T : ℕ → Era) (L : Columns C W d) (F : Price.Representatives C L)
open Market

-- Same b, calibration matrix, budget allocations. Reconstruction conditional producers on ONE paid sequence.
-- Models hypotheses upstream of corrected/H labels. No corrected moments demanded.
def uses (v : Fin (L.dim+1) → C.label d) (i : Fin L.amount) (j : Fin (L.dim+1)) := fun s : Fin ((L.row i).extra+1) => v (Columns.Trials.names (X:=L) i j s)
lemma actual (i j) : joint (uses L F.rep i j)= Market.roles L i j := by
  ext1 s; unfold uses joint Market.roles; rw [F.projection]





end YM.Next.Rank.Atlas
