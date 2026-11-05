import YM.OPE.Columns.Plane
import YM.OPE.Rate

/-!
# Re-announce an output of the low engineering transverse cost

Keep the literal Wdff cylinders of degree d. Back on the very same bare meshes and with
support and all weights (power & order, and Slot metric) charged there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Columns
open Function Set Filter RG Wilson Lattice Labels Source MergeProof Bid Push.RelayDifference Extraction
open Work.G08 Extra.Histories Cells
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {W r D} (T : TableTickets C W r D) {d e : ℕ}
    {l : Extraction.Order} (hx : C.Makes)
set_option quotPrecheck false
local notation "Q" => C.path.levels
local notation "T₀" => C.localSection d
local notation "F" => C.labels.level d
local notation "α" => C.S.a
local notation "K!" => fun i : Cutoffs => (C.factory d i.1 i.2).terminal
local notation "J" => juice C.path.levels

lemma juice_rate (C : Family G) : RateIs atTop C.S.scale (juice C.path.levels) 0 :=
  ⟨Eventually.of_forall fun i => (Ribbons.futon C).pos i,(Ribbons.futon C).pitch⟩

lemma slow_juice : Slow C l fun i => J i.1 :=
    (juice_rate C|>.pays C.S.divergent).comp (cutoff_grows l)

include hx T
/-- Cutoff points of the transported plane can be knots as large as allowed in d.
Given boundedness of their reference values, the *bare* cost can be charged at e.
No bound on the primary representation at coarser meshes of horizon e yet. -/
lemma weight_cost (v : Rowe C d) {M : ℝ} (hM : ∀ᶠ i in l.fuse, ‖v i‖ ≤ M)
    (ht : ∀ᶠ i in l.fuse, low F e (((K!) i).symm (v i))=((K!) i).symm (v i))
    (he : e<d) : Slow C l (fun i => ((α i.1:ℂ)^(d-e))⁻¹ • (((K!) i).symm (v i))) := by
  let b := ((α) (C.ref d)^(d-e))⁻¹ * ((F).extra+1:ℕ) * M
  apply (((slow_juice (C:=C) (l:=l)).mul (Slow.const b))).reduce
  filter_upwards [ht,hM, (cutoff_grows l).eventually_ge_atTop (C.ref d)] with i hi hx' hk
  let x:= ((K!) i).symm (v i); let a:= (α) i.1; let t:= d-e; let u:= (α) (C.ref d)
  have hy : OPE.Columns.trace C d i.1 i.2 (C.ref d) x = v i := (readTerminal hx hk x).trans (((K!) i).apply_symm_apply _)
  have hJ:=juice_pos Q i.1
  have ha : 0 < a := C.S.a_pos i.1; have hu : 0 < u := C.S.a_pos _
  have hp : (u/a)^t * ‖x‖ ≤ (J i.1)*(((F).extra+1:ℕ)*M) := calc
    _ ≤ (u/a)^t * (F).coeffSize x := mul_le_mul_of_nonneg_left (Size.norm_le ..) (by positivity)
    _ ≤ (J i.1)*(F).coeffSize (v i) := by
      have hw := top_shrunk (p:=i.2) T hx hi he le_rfl hk; rw [hy] at hw; exact hw
    _ ≤ _ := mul_le_mul_of_nonneg_left ((Size.le_norm F (v i)).trans (by
            rw [show Fintype.card ((F).Index)=_ from Fintype.card_fin ((F).extra+1)];
            exact mul_le_mul_of_nonneg_left hx' (by positivity))) (by linarith)
  change ‖((a:ℂ)^t)⁻¹ • x‖ ≤ ‖J i.1 * b‖
  rw [norm_smul,norm_inv,norm_pow, Complex.norm_real,Real.norm_of_nonneg ha.le]
  refine le_trans ?_ (Real.le_norm_self _)
  dsimp only [b]
  rw [div_pow,div_eq_mul_inv,mul_assoc] at hp
  change _ ≤ J i.1 * ((u^t)⁻¹ * ((F).extra+1:ℕ) * M)
  calc
    _ = (u^t)⁻¹ * (u^t * ((a^t)⁻¹ * ‖x‖)) := by rw [inv_mul_cancel_left₀ (by positivity : u^t ≠ 0)]
    _ ≤ _ := (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (u^t)⁻¹)).trans_eq (by ring)

lemma reannounce (hG : G.Simple) (v : Rowe C d) {M : ℝ} (hM : ∀ᶠ i in l.fuse, ‖v i‖ ≤ M)
    (ht : ∀ᶠ i in l.fuse, low F e (((K!) i).symm (v i))=((K!) i).symm (v i))
    (he : e<d) : RawProtected C l (Bid.upper C v) e := by
  let w : Rowe C d := fun i => ((α i.1:ℂ)^(d-e))⁻¹ • v i
  have hw : dollar C l w := (dollar_slow w).2 ((weight_cost T hx v hM ht he).reduce
    (Eventually.of_forall fun i => by simp [w]))
  have hp : RawProtected C l (Bid.upper C w) d := RawProtected.upper hx hG w hw
  have heq (N p : ℕ) (o) : unpriced C (Bid.upper C v) e N p o=unpriced C (Bid.upper C w) d N p o := by
    unfold unpriced Bid.upper
    simp only [w, ((C.linearO ..).map_smul ..)] -- arguments inferred?
    unfold Push.RelayDifference.weight; rw [smul_smul]
    congr 1
    have hh : d = e+(d-e) := by omega
    apply Eq.symm
    rw [mul_inv_eq_iff_eq_mul₀]
    · nth_rw 1 [hh]; rw [pow_add]
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
  simpa only [RawProtected,heq] using hp
end YM.OPE.Columns
