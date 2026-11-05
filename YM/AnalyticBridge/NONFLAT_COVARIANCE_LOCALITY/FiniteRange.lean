import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Either
import YM.Push.SECTOR_MEASURE.Presented

/-! # Finite range and complete dependency test for the covariance entries

Dependency charged from either endpoint on the actual full physical addresses,
where registration also includes every seed test (use `ReadsWithin`). Supports
can be taken uniformly in all sector arguments for these kernels, with
constants numerical post-L. The smaller extent is the *numerical range*
(sufficient also when estimating the inverse powers). Never use only that
when retaining a support. In particular even when A flags become genuine only
in a subpatch, can consume there with the same windows as computing any
consistent outer completion, if all touched window entries are paid. Allocate
all endpoints of the stencil tests in `ReadsWithin` (not just identities of
where queried). No term accounting for support of later polymer reconnection
attempted here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality.Matching
open Function Filter Lattice RG Pressure Pressure.Stores Precision Wilson Tree Matrix
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Wisps Next.Fluctuations
open Next.SectorChange.Completion Next.SectorChange.Rows Full Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

abbrev Reading (S : StepData c f) (G : Gauge) :=
  Stores S → Forest S.ratio → Config G c → S.Choices → Gaussian.Table (Index G f)
structure Local (E : Reading S G) (reach cost : ℕ) : Prop where
  far (A F V k i j) : ¬ separation (point S i) (point S j) ≤ reach → E A F V k i j = 0
  both {o r A B F H V W k k'} : ReadsWithin o r A B F H V W k k' → ∀ i,
    separation o (point S i)+cost ≤ r → ∀ j, E A F V k i j=E B H W k' i j ∧
      E A F V k j i=E B H W k' j i

namespace Local
variable {E Q : Reading S G} {l r t u : ℕ}


lemma sym (H : Local E l r) : Local (fun A F V k => (E A F V k).transpose) l r :=
  ⟨fun A F V k i j h => H.far A F V k j i (by rwa [separation_comm]),
   fun hp i h j => ⟨(H.both hp i h j).2,(H.both hp i h j).1⟩⟩
lemma scale (H : Local E l r) (t : ℝ) : Local (fun A F V k => t • E A F V k) l r :=
  ⟨fun A F V k i j h => by simp [H.far A F V k i j h],fun hp i h j =>
    ⟨congr_arg (fun v : ℝ => t • v) (H.both hp i h j).1,
     congr_arg (fun v : ℝ => t • v) (H.both hp i h j).2⟩⟩
lemma add (H : Local E l r) (h : Local Q l r) : Local (fun A F V k => E A F V k+Q A F V k) l r :=
  ⟨fun A F V k i j he => by simp [H.far A F V k i j he,h.far A F V k i j he],
   fun hp i he j => ⟨congr_arg₂ (fun v w : ℝ => v+w) (H.both hp i he j).1 (h.both hp i he j).1,
     congr_arg₂ (fun v w : ℝ => v+w) (H.both hp i he j).2 (h.both hp i he j).2⟩⟩
lemma one (S : StepData c f) (G : Gauge) (b c : ℕ) :
    Local (fun _ _ _ _ => 1 : Reading S G) b c :=
  ⟨fun A F V k i j h => Matrix.one_apply_ne (fun e => h (by simp [e])),fun _ _ _ _ => ⟨rfl,rfl⟩⟩

lemma top (H : Local E l r) (h : Local Q t u) :
    Local (fun A F V k => E A F V k * Q A F V k) (l+t) (max (r+t) (u+l)) := by
  refine ⟨fun A F V k i j he => ?_,?_⟩
  · simp only [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hp : separation (point S i) (point S b) ≤ l
    · have hh : ¬ separation (point S b) (point S j) ≤ t := fun hj =>
        he ((separation_triangle _ (point S b) _).trans (Nat.add_le_add hp hj))
      rw [h.far A F V k b j hh,mul_zero]
    rw [H.far A F V k i b hp,zero_mul]
  intro o c A B F F' V W k k' hp i he j
  have ht : r+t ≤ max (r+t) (u+l) := le_max_left ..
  have hu : u+l ≤ max (r+t) (u+l) := le_max_right ..
  simp only [Matrix.mul_apply]
  constructor <;> refine Finset.sum_congr rfl fun b _ => ?_
  · rw [(H.both hp i (by omega) b).1]
    by_cases hh : separation (point S i) (point S b) ≤ l
    · have hy := separation_triangle o (point S i) (point S b); rw [(h.both hp b (by omega) j).1]
    rw [H.far _ _ _ _ i b hh,zero_mul,zero_mul]
  rw [(h.both hp i (by omega) b).2]
  by_cases hh : separation (point S b) (point S i) ≤ t
  · have hy := separation_triangle o (point S i) (point S b); rw [separation_comm] at hh
    rw [(H.both hp b (by omega) j).2]
  rw [h.far _ _ _ _ b i hh, mul_zero,mul_zero]
end Local

variable {P : Teller G} {T : Tube G S}

lemma accessible (hp : P.Funds S T) (x : ℝ) : Local (here x T) (extent S.patch x) (room S.patch x) :=
  ⟨fun A F V k i j h => deck_quiet (funds_branch hp) x T A F V k i j h,
    fun h i ht j => ⟨h.here_first hp i ht j,h.here_last hp i ht j⟩⟩

lemma far_meeting (S : StepData c f) {x : ℝ} {i j : Index G f} (h : j∈groupWindow G S x i) :
    separation (point S i) (point S j) ≤ radiusB x/20 := h _ (Set.mem_insert _ _) _ (Set.mem_insert _ _)

private lemma pane_head {o z E H Q B V W k k'} (h : ReadsWithin (S:=S) (G:=G) o z E H Q B V W k k')
    {f : Reading S G} {r t : ℕ} (H' : Local f r t) (hx : 120 ≤ radiusB x) (u : ℝ) {i}
    (ht : separation o (point S i)+radiusB x/20+t ≤ z) (j) :
    panes (groupWindow G S x) u (f E Q V k) j i=panes (groupWindow G S x) u (f H B W k') j i := by
  let p := groupWindow G S x
  have he := per_self (full_bars (G:=G) (S:=S) hx) i
  by_cases hz : j∈p i
  · have hh : Schur.principal (f E Q V k) (p i)=Schur.principal (f H B W k') (p i) := by
      ext a b; have hb := far_meeting S a.property
      have hi := separation_triangle o (point S i) (point S a.val)
      exact (H'.both h a (by omega) b).1
    change panes p u _ _ _=panes p u _ _ _
    rw [read_panes p u _ i j he hz,read_panes p u _ i j he hz, hh]
  exact (hidden_pane p u _ hz).trans (hidden_pane p u _ hz).symm

lemma paned {f : Reading S G} {r t : ℕ} (h : Local f r t) (u : ℝ) (hx : 120 ≤ radiusB x) :
    Local (fun A F V k => panes (groupWindow G S x) u (f A F V k)) (radiusB x/20) (t+2*(radiusB x/20)) := by
  refine ⟨fun A F V k i j hh => hidden_pane (groupWindow G S x) _ _
    (fun hj => hh ((separation_comm ..).trans_le (far_meeting S hj))),fun {o z A B F H V W k k'} he i hi j => ?_⟩
  refine ⟨?_,pane_head he h hx u (by omega) j⟩
  by_cases hg : i∈groupWindow G S x j
  · have ht := far_meeting S hg; have hy := separation_triangle o (point S i) (point S j)
    rw [separation_comm] at ht; exact pane_head he h hx u (by omega) i
  exact (hidden_pane _ u _ hg).trans (hidden_pane _ u _ hg).symm

abbrev mass (x : ℝ) (S : StepData c f) := room S.patch x + 2*(radiusB x/20)
abbrev farCost (x : ℝ) (S : StepData c f) := max (room S.patch x+radiusB x/20) (mass x S+extent S.patch x)
abbrev nearCost (x : ℝ) (S : StepData c f) := extent S.patch x+radiusB x/20

lemma cloud_local (hp : P.Funds S T) (h : 120 ≤ radiusB x) :
    Local (fun A F V k => clouded (groupWindow G S x) (here x T A F V k)) (radiusB x/20) (mass x S) := by
  have hh := paned (accessible hp x) 0 h
  simp_rw [panes_zero] at hh
  exact (hh.add hh.sym).scale (1/2)
lemma deviations_local (hp : P.Funds S T) (h : 120 ≤ radiusB x) :
    Local (fun A F V k => deviation (here x T A F V k) (clouded (groupWindow G S x) (here x T A F V k)))
      (nearCost x S) (farCost x S) := by
  have hf := ((Local.one S G (nearCost x S) (farCost x S))).scale (-1)
  simp_rw [neg_smul,one_smul] at hf
  simp_rw [deviation,sub_eq_add_neg]
  exact ((accessible hp x).top (cloud_local hp h)).add hf


/-- allowances; `farCost` etc leave endpoint halo slack.
Used independently of the next B; no earning at other periods. -/
lemma local_extent (P : Patch) : ∀ᶠ x : ℝ in atTop,
    extent P x ≤ radiusB x/100 ∧
    ∀ {c f : Side} (S : StepData c f), S.patch=P →
      room P x ≤ mass x S ∧ mass x S ≤ farCost x S ∧ farCost x S + 10 ≤ 16*radiusB x ∧
      nearCost x S + 10 ≤ radiusB x/10 := by
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (10000*(predReach P+5))] with x hx
  have hh : extent P x ≤ radiusB x/100 := by unfold extent span till; omega
  refine ⟨hh,@fun c f S h => ?_⟩
  unfold nearCost farCost mass; rw [h]; unfold room; omega
end YM.AnalyticBridge.NonflatCovarianceLocality.Matching
