import YM.RG08.Spin.Air
/-!
# Input graph orientation in the pinned color, derivative, Frame conventions. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{H:Hol G}{S:SectionData F} {c : Side}{s:Signed}
lemma scope_a (b:Letter F) (V: ReadsU F D R) (e r:ℕ) (s:Signed) : bureau V (fluxO s F D) b e r=∑ i∈(univ:Finset (Letter F)).filter (sameO b),bankO s F D i b • V i e r:= by
    unfold bureau; rw [accounting]; let T i:=bankO s F D i b; simp_rw [isFlux]
    have hx(i): (∑ n∈range (e+1),(if n=0 then T i else 0) • V i (e-n) r)=T i • V i e r:= by rw [sum_eq_single_of_mem 0 (by simp)]; simp; intro j _ hj; rw [if_neg hj,zero_smul]
    rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun i _=> ?_; rw [hx i]; split_ifs with h; rfl
    rw [show T i=0 from if_neg (mt (sym_so b i).2 h),zero_smul]
lemma setSl_bill (H:Hol G)(S:SectionData F)(hp:S.Sound H)(s:Signed) (b:Letter F)(i : Site c)(v: Link G c) : setSl S b c i (input G c (orderTurn s v))=∑ j∈degreeT F b.label, actor F s j b.label*(S.places (Place.copy F j) (s.act i) (input G c v)).re:= by
    let L (M:F.Coeff):= S.places M (s.act i) (input G c v); let q:F.Coeff→ₗ[ℂ] ℂ:= {
       toFun:=L
       map_add' := fun x y => congr_fun (S.eval_linear.1 x y) (expandAt (s.act i) (input G c v))
       map_smul' := fun x y => congr_fun (S.eval_linear.2 x y) (expandAt (s.act i) (input G c v)) }
    change Complex.re (S.places _ _ _)=_; rw [← show L (F.act s.ortho (Place.copy F b.label)) = S.places (Place.copy F b.label) i (input G c (orderTurn s v)) from ?_, spreadsF s b.label]; swap
    · unfold L; rw [show s.act i=affine s 0 i from (add_zero ..).symm,← SectionData.placed_signed S hp s]; exact congr_arg _ (flip_links ..)
    change Complex.re (q _) =_; rw [map_sum, Complex.re_sum]
    apply Finset.sum_congr rfl; intro a _; rw [map_smul,smul_eq_mul,Complex.re_ofReal_mul]; rfl
-- echo orientation commute rooted representative. Extend linearly PER coefficient.
private def zed (S:SectionData F)(i: F.Index)(n:Side)(o: Site n)(v : Link G n):= (S.places (Place.copy F i) o (input G n v)).re
lemma sp_arc (H:Hol G)(S:SectionData F)(hp:S.Sound H)(s:Signed)(b:Letter F)(i:Site c)(v:Link G c)(n:ℕ):
    rootSong (crownP S b n) c i (orderTurn s v)=∑ j∈degreeT F b.label,actor F s j b.label* Tensor.diagonal (Tensor.coeff (zed S j c (s.act i)) n 0) v:= by
    let Z:= setSl S b c i ∘ input G c; let g j:= zed S j c (s.act i)
    let f j:= actor F s j b.label • g j
    have hz j: ContDiffAt ℝ n (g j) 0:= by
       let B:Letter F:= ⟨j,(0: Cham),by simp [cashT]; exact F.bound j⟩
       exact (smooth_sl S B (s.act i)|>.contDiffAt.of_le le_top) -- shadow I
    have hf: Z ∘ orderTurn s = ∑ j∈degreeT F b.label,f j := funext (fun p=> (setSl_bill H S hp s b i p).trans (by rw [Finset.sum_apply]; rfl))
    unfold rootSong; rw [crown_pays]; change Tensor.diagonal (Tensor.coeff Z _ _) (orderTurn s v) = _
    have ht: ContDiffAt ℝ n Z 0 := (smooth_sl ..).contDiffAt.of_le le_top
    have hx: Tensor.diagonal (Tensor.coeff Z n 0) (orderTurn s v)=Tensor.diagonal (Tensor.coeff (Z ∘ orderTurn s) n 0) v:= by unfold Tensor.diagonal Tensor.coeff; exact (congr_arg ((n.factorial:ℝ)⁻¹ * · : ℝ→ℝ) (DFunLike.congr_fun (Next.Foundations.jets_linear (orderTurn s) ht) (fun _=>v))).symm -- metavars
    rw [hx,hf,Tensor.coeff_sum]; unfold Tensor.diagonal; rw [_root_.sum_apply]; refine Finset.sum_congr rfl fun j hj=>?_; unfold f; rw [Tensor.coeff_smul _ (hz j)]; rfl
    intro j hj; exact (hz j).const_smul (actor F s j b.label)
-- input Section exactly honors this orientation
abbrev Spun (s:Signed)(V:ReadsU F D R) : Prop:= ∀ b,∀ n:Side,Honor s (bureau V (fluxO s F D) b) (V b) n
theorem outlines (H:Hol G)(S:SectionData F)(he:S.Sound H)(s:Signed) (hp:d≤D)(hr:0≤R): Spun s (fun i=> startU S i hp hr) := by
    let V i:= startU S i hp hr
    intro b n i φ k r v
    let U:= bureau V (fluxO s F D)
    let E := plug φ R
    let T:= twisting s φ
    let Z:= (univ:Finset (Letter F)).filter (sameO b)
    let x j:=actor F s j b.label; let q a:= appoint b.test (twisting s (coinsT D a))
    let m j:= Tensor.diagonal (Tensor.coeff (zed S j n (s.act i)) r 0) v
    change rootSong (E ∘ U b k r) n (s.act i) v= _; rw [show E ∘ U b k r= _ from (congr_arg (fun v: EnvelopeU D R G r=> E ∘ v) (scope_a b V k r s)).trans (graft ..)] -- expose lhs first
    let P (c:Letter F):= bankO s F D c b; let W c:=plug φ R∘ (P c • V c k r)
    change rootSong (∑ x∈Z,W x) n _ _= rootSong (plug T R∘ startU S b hp hr k r) n i (orderTurn s v)
    have hV b:Pens (V b k r):= (start_tid ..).pens
    rw [root_sum _ _ _ (fun j _=> ((hV j).scale (P j)).shaped _),Finset.sum_apply,echo_start]
    have hE (a:Letter F) (ha:a∈Z): rootSong (W a) n (s.act i) v=(P a)*rootSong (E ∘ V a k r) n (s.act i) v := by
       rw [show W a=P a • (E ∘ V a k r) from funext fun i=> by simp [W,E], root_scale _ ((hV _).shaped _)]; rfl
    rw [Finset.sum_congr rfl hE]
    split; next ht=>
       rw [root_scale _ ((crown_tidy ..).pens)]; change _= chant b hp hr T* _; rw [sp_arc H S he s b i v r]; change _ = chant b hp hr T * ∑ j∈degreeT F b.label,x j*m j
       symm; rw [ap_sl b _ _ T,ap_turn s b.test φ ((le_trans (Nat.le_add_left ..) b.bill).trans hp)] -- T=rfl wrong
       simp only [Finset.mul_sum, Finset.sum_mul]; refine spin_sum b _ _ fun a ha=> ?_
       rw [show P a = x a.label*q a.test from if_pos ((sym_so b a).1 ha)]; unfold V E
       rw [echo_start,if_pos (by rw [← (sameF ha).2,ht]),root_scale _ ((crown_tidy ..).pens)]; unfold rootSong; rw [crown_pays]
       change _ = x a.label*q a.test*(appoint a.test φ*m a.label); unfold q; ring
    next ht=> rw [root_zero]; refine Finset.sum_eq_zero fun a ha=> ?_; have hh:= (scope_b ..).1 ha; unfold V E; rw [echo_start,if_neg (by rw [← (sameF hh).2]; exact ht),root_zero,Pi.zero_apply,mul_zero]
end YM.RG08.Spin
