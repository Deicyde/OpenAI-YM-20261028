import YM.UVExtension.Fallow.Tumble
import YM.MergeProof.Biscuit
import YM.MergeProof.Straw
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.Mulch
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open UVExtension.Fallow
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid Mix Source Labels
  Next.Foundations Attach Opening Planned.GuardedAtom Guard YM.MergeProof
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {C : Family G} {N p d : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C}
variable {u : ℕ → ℝ}{ζ:ℕ → ℕ → ℝ}
set_option quotPrecheck false
lemma persistsR {V:Stem C p} (hc:Vintage.YM.Family.Makes C) (K : G.Simple) (hZ:∀ N p:ℕ,Nonempty (Keeper (C.path.rep N p N).p (C.path.rep N p N).activities)) (hp:roof C Extraction.Order.full) (hu:∀ i,0  <  u i)(hx:Slow C Extraction.Order.full fun i=> (u i.1)⁻¹) (hv:Slow C Extraction.Order.full fun i=> ζ d i.1)(hr:∀ i,C.ref d ≤ i → 0 ≤ ζ d i)
    (h:garment V d)(ht:∀ᶠ i in atTop,Continuous (V i)) : ∃ E:ℕ → ℝ, Rested C E ∧ ∀ᶠ i in atTop,C.ref d  ≤  i ∧ ∃ Z t Q, Cream C i p d u ζ (V i) Z Q t (E i):=by
  classical
  let H := C.path
  let L := C.labels.level d
  let T := C.localSection d
  obtain ⟨X,hX,c,b,hc',hb,H'⟩ := h
  let D := X ∪ T.stencil
  obtain ⟨k,hk,h₁⟩ := price_of_readout C.params L
  obtain ⟨t,ht',h₂⟩ := offmask C d
  let score (j : ℕ) := k*c j
  let r (j : ℕ) := badCost C d j t (score j) (b j)
  let g (j : ℕ) := regCost C j (score j) (c j)
  let M : ℝ := 2*D.card
  let A (j : ℕ) := Real.exp ((H.levels.params j).supportExponent) ^ (81:ℕ)
  let Att (j : ℕ):= A j* Real.exp (162:ℝ)*r j
  let box (j : ℕ) := A j*(g j+r j*M)
  let total (j : ℕ) := 1 + (box j + score j); let BaseE (j : ℕ):=4*(1+(C.path.levels.params j).columns)*total j; let E (j : ℕ):= BaseE j + Att j*(ζ d j)*(u j)⁻¹
  have hs : Rested C (fun j=> score j):=(Slow.const k).mul hc'; have ho:Rested C r:= hb.add (((Slow.const (C:=C) ((2:ℝ)*t)).mul (seats_slow K)).mul hs); have hA := Slow.pow hp 81
  have hm: Rested C total := (Slow.const (C:=C) (1:ℝ)).add ((hA.mul ((hc'.add (columns_slow.mul hs)).add (ho.mul (Slow.const M)))).add hs)
  refine ⟨E,(((((Slow.const (C:=C) (4:ℝ)).mul ((Slow.const _).add columns_slow)).mul hm)).add (((((hA.mul (Slow.const _)).mul ho).mul hv)).mul hx)),?_⟩
  let F : Trial C:= fun N p'=> if h:p'=p then h ▸ fun o=> V N else 0
  have hm n: F n p 0= V n:=by simp [F]
  filter_upwards [cover_tops (C:=C) K D, ht, eventually_ge_atTop (C.ref d), mitt (C:=C) K D,H'] with i hi hP hI hJ hV
  let N:=i; let z:= D; let o:= (0:Site (C.side N p)); let Y:=regional D o; let C':=C.path.rep N p N; let P:= C.path.levels.budget N; let v':= C.path.levels.clock.forcedAllowance N
  have hY:regional X o ⊆ Y := Finset.image_subset_image Finset.subset_union_left
  have hV:clothed P (regional X o) o (unpriced C F d N p 0) (c i) (b i):= by unfold unpriced; have hx:=hV o; rw [show bloom (V i) o=V i from home _] at hx; rw [hm]; exact hx
  obtain ⟨hy,hC,hB,hL⟩:= hV; have hG:=regular_larger hy hY; have hc'' := bound_larger hC hY; obtain ⟨Z,h,Zr,hK,hV, S,hS,Hx⟩:= Vintage.YM.Push.RelayDifference.saving C hc hI Y (Classical.choice (hZ N p)) (hJ p) (Finset.image_subset_image Finset.subset_union_right) F ⟨hG,hc'',hB,hL⟩ ht' h₂ (score:=score i) (fun z hz => h₁ _ o Y P _ _ (Nat.le_of_succ_le ((Vintage.YM.Family.Makes.stages hc d).2 N hI).1) ((Vintage.YM.Family.Makes.stages hc d).2 N hI).2 hG hc'' z hz)
  have hY': (Y.card:ℝ) ≤ D.card:=by exact_mod_cast Finset.card_image_le
  have hp: (coverNumber P.B Y:ℝ) ≤ 81:=by exact_mod_cast hi p; -- exponent.N
  let a:ℝ:= Real.exp (P.supportExponent*coverNumber P.B Y)
  have he : a  ≤  A i:=by unfold a A;rw [← Real.exp_nat_mul]; apply Real.exp_monotone; push_cast;change _ ≤ 81*P.supportExponent;nlinarith only [hp,P.exponent_pos, mul_le_mul_of_nonneg_left hp P.exponent_pos.le]
  have hf : 0  ≤  v':=(Real.exp_pos _).le; have hz:Real.sqrt v' ≤ 1:=Real.sqrt_le_one.mpr (Extra.Histories.Doors.stain_le (C.path.levels.clock.hatBeta N))
  have hg : 0  ≤  score i := (coeff_pos L _).trans Zr; have hr' : 0 ≤  r i:= add_nonneg hB (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans ht')) (seats_nonneg ..)) hg); have hb:0  ≤  A i:= le_trans (Real.exp_pos _).le he
  have hφ:0  ≤  g i:= add_nonneg hC.1 (mul_nonneg (zero_le_one.trans (C.path.levels.params N).columns_ge) hg)
  have hv: 2*(Y.card:ℝ)*Real.sqrt v' ≤  M:= by
    exact (mul_le_of_le_one_right (mul_nonneg zero_le_two (Nat.cast_nonneg _)) hz).trans (mul_le_mul_of_nonneg_left hY' zero_le_two)
  have hf: quicksilver P Y (g i) (r i) v'  ≤  box i:=by
    change a*g i+2*(Y.card:ℝ)*_* (a*r i)  ≤  A i*(g i+r i*M)
    rw [mul_add (A i)]
    exact add_le_add (mul_le_mul_of_nonneg_right he hφ) ((mul_le_mul hv (mul_le_mul_of_nonneg_right he hr') (mul_nonneg (Real.exp_pos _).le hr') (show 0  ≤  M by unfold M; positivity)).trans_eq (by ring))
  have hU:YM.Push.Local.reservedMass P Y (r i)  ≤  Att i:=by
    unfold YM.Push.Local.reservedMass
    apply mul_le_mul_of_nonneg_right _ hr'; rw [add_mul,Real.exp_add]; apply mul_le_mul he _ (Real.exp_pos _).le hb; apply Real.exp_monotone; linarith only [hp]
  have hy:0  <  total i:=by
    have hx:0  ≤  M:=by unfold M; positivity
    exact add_pos_of_pos_of_nonneg zero_lt_one (add_nonneg (mul_nonneg hb (add_nonneg hφ (mul_nonneg hr' hx))) hg)
  have hAtt: 0 ≤  Att i:=(mul_nonneg (Real.exp_pos _).le hr').trans hU
  have hE:BaseE i  ≤  E i:=le_add_of_nonneg_right (mul_nonneg (mul_nonneg hAtt (hr N hI)) (inv_pos.mpr (hu N)).le)
  refine ⟨hI,Z,box i,total i,h,Extra.Histories.rem_mono hK hf, (add_le_add_left Zr _).trans (le_trans (add_comm ..).le (le_add_of_nonneg_left zero_le_one)),hy,hE, ⟨S,Att i,stackFee hS hU,?_,Hx⟩, by rw [hm] at hV; exact hV,hP⟩
  have hO:= hu N
  apply le_trans _ (mul_le_mul_of_nonneg_left (show BaseE i + Att i*ζ d N*(u N)⁻¹ ≤ E i from le_rfl) hO.le)
  have hm: 0  ≤  BaseE i:=mul_nonneg (mul_nonneg (by norm_num) (add_nonneg zero_le_one (zero_le_one.trans (C.path.levels.params _).columns_ge))) hy.le
  rw [mul_add,show u N * (Att i*ζ d N*(u N)⁻¹)=Att i*ζ d N from by field_simp]
  exact le_add_of_nonneg_left (mul_nonneg hO.le hm)
end YM.Push.RelayDifference
