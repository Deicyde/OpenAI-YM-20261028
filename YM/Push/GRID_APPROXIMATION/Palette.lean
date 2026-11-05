import YM.Push.GRID_APPROXIMATION.Candidates

/-!
# Finite basis of actual rooted requests, one system for the continuum of labels

Never retune histories for linear combinations. Treat the physical unit,
including its unusual reference coordinate, exactly at every translation.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson Labels Cells MeasureTheory Function Set Filter
open scoped Topology BigOperators

variable {G : Gauge} (C : Family G)

abbrev Ind (d : ℕ) := (C.labels.level d).Index

def slot (d) (x : C.label d) : C.book.Token := ⟨d,x⟩

def swatch (d) (i : Ind C d) := slot C d (Pi.single i 1)

lemma swatch_plain (d) (i : Ind C d) : star (swatch C d i).2=(swatch C d i).2 := by
  change star (Pi.single i 1 : C.label d) = Pi.single i 1
  ext j; by_cases h : j=i <;> simp [h]

-- The constant used at every station for basis index 0 (unit itself
-- scaled in basis coordinates; e0 corresponds to this value).

def oneColor (d : ℕ) := ((C.S.a (C.ref d):ℂ)^d)⁻¹

def onePaint (d h : ℕ) : Figures C (swatch C d 0) h where
  plot _ _ _ _ := oneColor C d
  cap _ := 1+‖oneColor C d‖
  err _ := 0
  radius _ := 0

lemma oneSeen (H : C.Makes) (d N p) (hN : C.ref d ≤ N) (o : Site (C.side N p)) :
    C.seen (swatch C d 0) o = fun _ => oneColor C d := by
  let α : ℂ := (C.S.a (C.ref d):ℂ)^d
  have he : α • C.seen (swatch C d 0) o=1 := by
    unfold Family.seen swatch slot; dsimp only; rw [← (C.linearO N p d o).map_smul]
    exact C.constant H d hN o
  funext U
  have hp : α * C.seen (swatch C d 0) o U = 1 := congr_fun he U
  exact eq_inv_of_mul_eq_one_right hp

lemma oneGives (hC : C.Makes) (f : Extraction.Order) (d h : ℕ) : (onePaint C d h).Gives f := by
  let v := swatch C d 0
  refine ⟨swatch_plain ..,fun q => ?_,fun _ => le_rfl,fun _ => le_rfl,tendsto_const_nhds,tendsto_const_nhds,fun q => ?_⟩
  · unfold onePaint; dsimp only; positivity
  have he := original_late C hC f h v
  unfold Extraction.Order.late at *
  filter_upwards [he] with k hk
  filter_upwards [hk] with j hj
  obtain ⟨ht,hN,hV⟩ := hj
  have hx : ∀ N p U, (onePaint C d h).plot q N p U = oneColor C d := fun _ _ _ => rfl
  refine ⟨hN,ht,hV,Interior.constant _ _,⟨0,by simp [onePaint],Interior.constant _ _⟩,fun U => ?_,fun U => ?_,?_⟩
  · change ‖oneColor C d‖ ≤ 1+‖oneColor C d‖; linarith
  · simp [hx,oneColor]
  rw [oneSeen C hC d (f.mesh j) (f.per k) ht]
  let T := tilesAt C.S (f.per k) hN
  change T.rootTest _ ((fun _ => oneColor C d) - fun _ => oneColor C d) ≤ 0
  rw [sub_self]
  let X := (0 : Config G (C.side (f.mesh j) (f.per k)) → ℂ)
  have hh := Next.Extract.root_smul T (C.beta (f.mesh j) (f.per k)) X 0
  simp only [smul_zero,norm_zero,zero_mul,X] at hh
  exact hh.le

variable {C} {d h : ℕ}

/-- One palette fixes finite-volume witnesses before **all** linear and
product queries, even when later uses invoke arbitrarily many real v through
this degree. -/
def palette (Z : ∀ i : Ind C d, Figures C (swatch C d i) h) (v : C.label d) : Figures C (slot C d v) h where
  plot a N p := ∑ i, v i • (Z i).plot a N p
  cap a := 1 + ∑ i, ‖v i‖ * (Z i).cap a
  err a := ∑ i, ‖v i‖ * (Z i).err a
  radius a := ∑ i, (Z i).radius a



lemma seen_combination (v : C.label d) (N p) (x : Site (C.side N p)) :
    C.seen (slot C d v) x = ∑ i, v i • C.seen (swatch C d i) x := by
  let A := (C.linearO N p d x).mk' _
  change A v = ∑ i, v i • A _
  have he := congr_arg A (coeff_sum C v)
  simp only [map_sum,map_smul] at he
  exact he.symm

lemma palette_gives (Z : ∀ i : Ind C d, Figures C (swatch C d i) h) (H : C.Makes)
    {f : Extraction.Order} (hz : ∀ i, (Z i).Gives f) (v : C.label d) (hv : star v=v) : (palette Z v).Gives f := by
  let r (i : Ind C d) := ‖v i‖
  refine ⟨hv, fun q => ?_, fun q => ?_, fun q => ?_, ?_, ?_, fun q => ?_⟩
  · have he : 0 ≤ ∑ i, ‖v i‖ * (Z i).cap q := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hz i|>.cap_pos q).le
    exact add_pos_of_pos_of_nonneg one_pos he
  · change 0 ≤ ∑ i, ‖v i‖ * (Z i).err q
    exact Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hz i|>.err_nn q)
  · change 0 ≤ ∑ i, (Z i).radius q
    exact Finset.sum_nonneg fun i _ => hz i|>.radius_nn q
  · have he (i : Ind C d) : Tendsto (fun a => r i * (Z i).err a) atTop (𝓝 0) := by
      simpa only [mul_zero] using (hz i).cost.const_mul (r i)
    simpa only [Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun i _ => he i)
  · simpa only [Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun i _ => (hz i).shrinks)
  have he (i : Ind C d) := (hz i).late q
  let K := slot C d v
  have hV := original_late C H f h K
  unfold Extraction.Order.late at *
  filter_upwards [eventually_all.mpr he,hV] with k hk hh
  filter_upwards [eventually_all.mpr hk,hh] with j hj hl
  obtain ⟨hb,hw,hI⟩ := hl
  let N := f.mesh j; let p := f.per k
  let T := tilesAt C.S p hw
  let β := C.beta N p
  let U (i : Ind C d) := (Z i).plot q N p
  let V (i : Ind C d) : Config G (C.side N p) → ℂ := C.seen (swatch C d i) 0
  let W (i : Ind C d) := U i - V i
  let L := (palette Z v).plot q N p
  have hT := seamless H N p
  have hn (i : Ind C d) : Interior (T.chamber 0) (U i) := (hj i).target
  have hy (i : Ind C d) : Interior (T.chamber 0) (W i) := by
    unfold W; rw [sub_eq_add_neg]
    have he' : Interior (T.chamber 0) (V i) := (hj i).source
    exact (hn i).plus (show Interior _ (fun U => -_) from by simpa using he'.scale (-1))
  have ht := Next.Extract.rooted T β hT Finset.univ W v fun i _ => hy i
  have hs : Interior (T.chamber 0) L := (Next.Extract.rooted T β hT Finset.univ U v fun i _ => hn i).1
  refine ⟨hw,hb,hI,hs,?_,fun x => ?_,fun x => ?_,?_⟩
  · choose w hw' hJ using fun i => (hj i).short
    let l := ∑ i, w i
    have he' (i : Ind C d) : Interior (window 0 l) (v i • U i) := by
      apply Interior.scale
      apply (show Interior _ (U i) from hJ i).enlarges
      rintro x ⟨y,hy,rfl⟩
      have hx : w i ≤ l := Finset.single_le_sum (fun i _ => Nat.zero_le (w i)) (Finset.mem_univ i)
      exact ⟨y,box_larger hy hx,rfl⟩
    have hX (s : Finset (Ind C d)) : Interior (window 0 l) (∑ i∈s,v i • U i) := by
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; exact Interior.constant _ _
      | insert i s hi ih => rw [Finset.sum_insert hi]; exact (he' i).plus ih
    refine ⟨l, ?_, hX Finset.univ⟩
    unfold l; rw [Nat.cast_sum,Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hw' i
  · change ‖(∑ i,v i • U i) _‖ ≤ 1+∑ i,r i*(Z i).cap q; rw [Finset.sum_apply]
    apply le_trans (norm_sum_le ..) (le_trans (Finset.sum_le_sum ?_) (le_add_of_nonneg_left zero_le_one))
    intro i _; simp only [Pi.smul_apply, norm_smul]; exact mul_le_mul_of_nonneg_left ((hj i).bound x) (norm_nonneg _)
  · change star ((∑ i,v i • U i) _) = _
    change star ((∑ i,v i • U i) _) = (∑ i,v i • U i) _
    have hp i : star (v i)= v i := congr_fun hv i
    have hU i : star (U i x)=U i x := (hj i).real x
    simp only [Finset.sum_apply,star_sum,Pi.smul_apply,smul_eq_mul,star_mul,hp,hU]; simp_rw [mul_comm (U _ x)]
  · change T.rootTest β ((∑ i,v i • U i)-C.seen (slot C d v) 0) ≤ ∑ i,r i * (Z i).err q
    rw [seen_combination]; change T.rootTest β ((∑ i,v i • U i)- (∑ i,v i • V i)) ≤ _
    simp only [← Finset.sum_sub_distrib,← smul_sub]
    exact ht.2.trans <| Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ((hj i).cost) (norm_nonneg _)

/-- No additional charge for basis index zero. -/
lemma paints (H : C.Makes) (f : Extraction.Order) (d h : ℕ)
    (T : ∀ i : Ind C d, i≠0 → Supplies C f h (swatch C d i)) :
    ∃ (Z : ∀ i : Ind C d, Figures C (swatch C d i) h), Z 0 = onePaint C d h ∧ ∀ i, (Z i).Gives f := by
  classical
  have he (i : Ind C d) : ∃ P : Figures C (swatch C d i) h,
      (∀ hv : i=0, hv ▸ P = onePaint C d h) ∧ P.Gives f := by
    by_cases hh : i=0
    · subst i; exact ⟨onePaint C d h,fun _ => rfl, oneGives C H f d h⟩
    obtain ⟨z,hz⟩ := Candidates.provided C H f h (swatch C d i) (swatch_plain ..) (T i hh)
    exact ⟨z,fun hu => (hh hu).elim,hz⟩
  choose Z hZ hz using he; exact ⟨Z,hZ 0 rfl,hz⟩
end YM.Push.GridApprox
