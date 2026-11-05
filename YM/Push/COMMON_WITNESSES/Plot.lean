import YM.Next.FOUNDATIONS.SU2
import YM.Push.COMMON_WITNESSES.GridBills
import YM.Work.A15

/-!
# Use finite Grill receipts for all weight-bounded anti-products

Issue about uncountably many `v` in an extraction. Basis choices use only
fixed, ordinary real raw labels and we prove explicit transfer by
multilinearity. Must test mixed entries in the quantitative approximation
because `Works` itself is a quadratic predicate; for this purpose it wouldn't
suffice just to prove independent fillings for the basis by this argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Table Lattice MeasureTheory Next.Extract Wilson OS
open scoped Topology BigOperators ContDiff

variable {G : Gauge} {C : Family G}
variable {n : ℕ} (h : ℕ) (x : Fin n → Cover) (d : Caps n)

/-- All word slots at those grades. -/
abbrev tagged (v : C.book.Vector d) (i : Fin n) : C.book.Token := ⟨d i, v i⟩



def multiplier (v : C.book.Vector d) (i : Combo C d) : ℝ := ∏ p, (v p (i p)).re

private lemma slot_expansion (v : C.book.Vector d) (H : Grid.plain (C:=C) (tagged d v))
    (N p : ℕ) (L : ∀ i : Fin n, C.book.Ref (d i) →ₗ[ℂ] Config G (C.side N p) → ℂ) (q : Config G (C.side N p)) :
    ∏ i : Fin n, L i (v i) q = ∑ j : Combo C d, (↑(multiplier d v j):ℂ)*∏ i, L i ((baseWord C d j i).2) q := by
  let D i := Pi.basisFun ℂ ((C.labels.level (d i)).Index)
  let F := fun i (j : (C.labels.level (d i)).Index) => (↑((v i j).re) : ℂ)*(L i (D i j) q)
  have he (i : Fin n) (j : (C.labels.level (d i)).Index) : ((D i).repr (v i)) j=↑(v i j).re := by
    have he : (starRingEnd ℂ) (v i j) = v i j := congr_fun (H i) j
    rw [Pi.basisFun_repr,Complex.conj_eq_iff_re.1 he]
  have hp i : L i (v i) q=∑ j : (C.labels.level (d i)).Index, F i j := by
    have hu := congr_fun (congr_arg (L i) ((D i).sum_repr (v i))) q
    simpa only [map_sum,map_smul,he,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hu.symm
  simp_rw [hp]; rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold F multiplier; rw [Finset.prod_mul_distrib,Complex.ofReal_prod]
  rfl

lemma speaking (v : C.book.Vector d) (H : Grid.plain (C:=C) (tagged d v)) (N p t i : ℕ) (q : Config G (C.side N p)) :
    Grid.flash (C:=C) h (tagged d v) x N p t i q =
      ∑ s : Combo C d, (↑(multiplier d v s):ℂ) * Grid.flash (C:=C) h (baseWord C d s) x N p t i q := by
  let b : Cover := fun _ => t*i
  let M (a : Fin n) (y : Cover) : C.book.Ref (d a) →ₗ[ℂ] Config G (C.side N p) → ℂ :=
    (C.linearO N p (d a) (Cells.location C.S h N p (y+b))).mk' _
  let m := Signed.mirror timeAxis
  let Z a := M a (m.act (x a)) ∘ₗ C.book.mirrorGroup (d a) m
  unfold Grid.flash Grid.tiny
  simp only [mul_sub,Finset.sum_sub_distrib]
  apply congr_arg₂
  · exact slot_expansion d v H N p (fun i : Fin n => M i (x i)) q
  exact slot_expansion d v H N p Z q

lemma flash_cont (w : Fin n → C.book.Token) (N p t i : ℕ) : Continuous (Grid.flash (C:=C) h w x N p t i) := by
  unfold Grid.flash
  dsimp only
  have hy (w : Fin n → C.book.Token) (x u) : Continuous (Grid.tiny (C:=C) h w x N p u) :=
    continuous_finsetProd _ fun i _ => C.continuousO N p (w i).1 (w i).2 _
  apply Continuous.sub <;> apply hy

private lemma collected {α : Type*} {ι : Type*} {J : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι] [Fintype J]
    (v : ι → J → α → ℝ) (h : ∀ i j, Integrable (v i j) μ) (c : ι→J→ℝ) :
    (∫ a, ∑ i, ∑ j, c i j * v i j a ∂μ) = ∑ i, ∑ j, c i j * ∫ a, v i j a ∂μ := by
  have hc (i j) : Integrable (fun a => c i j * v i j a) μ := (h i j).const_mul _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hc i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hc i j)]; simp only [integral_const_mul]

lemma costs_flash (v : C.book.Vector d) (H : Grid.plain (C:=C) (tagged d v)) (N p t i j : ℕ) :
    Grid.bill (C:=C) h (tagged d v) x i j N p t =
      ∑ s : Combo C d, ∑ u : Combo C d, (multiplier d v s * multiplier d v u)*cross C h x d N p t i j s u := by
  let F (i : ℕ) (s : Combo C d) := Grid.flash (C:=C) h (baseWord C d s) x N p t i
  let L (s u : Combo C d) (q : Config G (C.side N p)) := (F i s q * F j u q).re
  have he s u : Integrable (L s u) (law G (C.side N p) (C.beta N p)) := continuous_integrable _
    (Complex.continuous_re.comp ((flash_cont h x (baseWord C d s) N p t i).mul (flash_cont h x (baseWord C d u) N p t j)))
  let A := multiplier d v
  have ht q : (Grid.flash (C:=C) h (tagged d v) x N p t i q * Grid.flash (C:=C) h (tagged d v) x N p t j q).re =
      ∑ s : Combo C d, ∑ u : Combo C d, (A s * A u)*L s u q := by
    simp_rw [speaking h x d v H,Finset.sum_mul,Finset.mul_sum,Complex.re_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    dsimp only [L,F,A]; simp [Complex.mul_re,Complex.mul_im]; ring
  unfold Grid.bill cross; simp_rw [ht]
  exact collected L he _

/-- Build the actual grid coverings. Track the scalar coefficients in the
bounds. The zeros and the empty product pose no additional budget requests. -/
def boundSum (v : C.book.Vector d) : ℝ := ∑ s : Combo C d, |multiplier d v s|

def onRails (v : C.book.Vector d) (A : GrillCosts) (P : Exhibit C d) : Grid.Covering (C:=C) h (tagged d v) x where
  plots k N p t i q := ∑ s, multiplier d v s * P k N p t i s q
  reserve k := boundSum d v * A.cap k
  small k := (boundSum d v)^2 * toll k
  grows := by simpa only [mul_zero] using toll_go.const_mul ((boundSum d v)^2)

variable (v : C.book.Vector d) {A : GrillCosts} {P : Exhibit C d}

lemma coherence {f : Extraction.Order} (H : Grid.plain (C:=C) (tagged d v)) (hx : Exhibits C h x d A f P) :
    Grid.Covering.Works h (tagged d v) x (onRails h x d v A P) f := by
  let R := boundSum d v
  let c := multiplier d v
  constructor
  · intro k t j
    refine (hx k t (j+1)).mono fun i hi => hi.mono ?_
    intro l hl
    let F := P k (f.mesh l) (f.per i) t
    change Measurable (fun q => ∑ s, c s * F j s q) ∧ ∀ q, |∑ s, c s * F j s q| ≤ R*A.cap k
    have he := hl.safe j (Nat.lt_succ_self _)
    refine ⟨Finset.measurable_sum _ (fun s _ => measurable_const.mul (he s).1),fun q => ?_⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold R boundSum
    rw [Finset.sum_mul]; refine Finset.sum_le_sum fun s _ => ?_
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((he s).2 q) (abs_nonneg _)
  intro k i j hij
  filter_upwards [eventually_ge_atTop (A.past k i j)] with t ht
  refine (hx k t (j+1)).mono fun r hr => hr.mono ?_
  intro l hl
  let N := f.mesh l
  let p := f.per r
  let μ := law G (C.side N p) (C.beta N p)
  let F := P k N p t
  let B s u (q : Config G (C.side N p)) := F i s q * F j u q
  have hp := hl.safe j (Nat.lt_succ_self _)
  have hq := hl.safe i (Nat.lt_succ_of_lt hij)
  have heI s u : Integrable (B s u) (law G (C.side N p) (C.beta N p)) :=
    Integrable.of_bound ((hq s).1.mul (hp u).1).aestronglyMeasurable (A.cap k * A.cap k)
      (Eventually.of_forall fun q => show |B s u q| ≤ _ from by
        unfold B; rw [abs_mul]; exact mul_le_mul ((hq s).2 q) ((hp u).2 q) (abs_nonneg _) (A.nonneg _))
  let L := (onRails h x d v A P).plots k N p t
  let E (s u : Combo C d) := (∫ q, B s u q ∂μ)-cross C h x d N p t i j s u
  change |(∫ q, L i q * L j q ∂μ)-Grid.bill (C:=C) h (tagged d v) x i j N p t| ≤ R^2 * toll k
  have he : (∫ q, L i q * L j q ∂μ) - Grid.bill (C:=C) h (tagged d v) x i j N p t =
      ∑ s, ∑ u, (c s*c u)*E s u := by
    have hE (q : Config G (C.side N p)) : L i q * L j q = ∑ s, ∑ u, (c s*c u)*B s u q := by
      unfold L onRails; dsimp only
      simp_rw [Finset.sum_mul,Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
      unfold c B F; ring
    simp_rw [costs_flash h x d v H N p t i j,hE]; rw [collected B heI _]
    simp only [E,mul_sub,Finset.sum_sub_distrib]; rfl
  rw [he]
  have hw : R^2*toll k = ∑ s : Combo C d, ∑ u, (|c s| * |c u|)*toll k := by
    unfold R boundSum; rw [pow_two]; simp_rw [Finset.sum_mul,Finset.mul_sum,Finset.sum_mul]; rfl
  rw [hw]; refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun s _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun u _ => ?_
  rw [abs_mul, abs_mul]; exact mul_le_mul_of_nonneg_left (hl.joins i j hij j.lt_succ_self ht s u)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))
end YM.Push.Common
