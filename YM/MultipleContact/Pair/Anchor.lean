import YM.MultipleContact.Pair.Extract
import YM.MultipleContact.Matching.Pocket

/-! Project the approaching same-Wilson pair at the second insertion using true continuum physical fields. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MultipleContact.Two
open Function Filter Set Metric Power Table Spec Extraction
open scoped Topology BigOperators Classical
open MergeProof.Acme YM.Next.UVStress
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Order}{n k:ℕ}{P:DiffPlan S}

structure Data (C:Family G)(F:Order)(S:Table C.book)(P:DiffPlan S) where
  simple : G.Simple
  fees : Matching.Matching C
  aroma : Aroma C
  seed : Seed C F S
  inclusion : P.Inclusions S
  deriv : P.Derivatives S
  turns : Rotation S
  oriented : turns.Oriented S

variable (H:Data C F S P)(A B:S.Tag)
def massDeg {L:Register G}{T:Table L}(A B:T.Tag):ℕ:=A.1+B.1
def gain : ℝ := 1/64
def kernelAnchor : FamilyData ℂ C.book:= fun e y z=> anchoredValue S A B e.letter y z
lemma gain_pos : 0 < gain:=by norm_num [gain]
include H
lemma anchor_price (ε:ℝ)(hε:0<ε): AtPrice (kernelAnchor A B) (-(massDeg A B:ℝ)-ε):=by
    intro e K hK hr
    let q(_:Unit):=e.letter; let f(x:Points e.n)(_i:Unit):= x
    have hf:Continuous f:= continuous_pi fun i=>continuous_id
    have hs(x)(hz:x∈f '' K)(u:Unit):Points.cons 0 (x u) ∈conf _:= by obtain ⟨w,hw,rfl⟩:=hz;exact hr w hw
    obtain ⟨r,hR,h⟩:=Local.pairOrdinary H.oriented q A B ε _ (hK.image hf) hs H.aroma H.fees H.deriv H.seed.kernel H.seed.generic H.seed.copies H.seed.cutoff H.simple hε
    refine ⟨1,zero_le_one,?_⟩
    filter_upwards [norm_eventually (E:=E4) r hR] with y ⟨hy₀,hy⟩ z hz
    have hv:=h (f z) (mem_image_of_mem f hz) (fun _=>1) (by simp) trivial y hy₀ hy
    have hTw:Local.combo q A B (fun _=>1) (f z) y=anchoredValue S A B e.letter y z:=by
       rw [anchoredValue,anchor_as_cons];unfold Local.combo fixedValue Local.twice Ward.disc; simp only [Finset.univ_unique,Finset.sum_singleton,one_mul,f,q]; rfl
    rw [hTw] at hv; unfold kernelAnchor massDeg; rw [one_mul, Nat.cast_add,show -((A.fst:ℝ)+(B.fst:ℝ))-ε=-(B.fst:ℝ)-(A.fst:ℝ)-ε from by ring]; exact hv

omit H
variable (k)(D:Detector S k)
-- augmented batch and coefficients
private def count (e:Exterior C.book) : Option D.probes → ℕ
 | none=>e.n
 | some i=> (i:Exterior C.book).n
private def probes (e:Exterior C.book) : ∀ i,Fin (count k D e i) → C.book.Token
 | none=>e.letter
 | some i=> i.val.letter
private def locs (e:Exterior C.book)(z:Points e.n): ∀i,Points (count k D e i)
 | none=>z
 | some i=>relative (i:Exterior C.book)
private lemma continuity_locs (e:Exterior C.book):Continuous (locs k D e):=by
 refine continuous_pi (fun i=>?_);cases i with
 | none=> exact continuous_id
 | some i=> exact continuous_const
private def principal (u:D.probes):S.Field k:=D.decode (Pi.single u 1)
private lemma decode_eval (f:D.probes→ℂ) : D.decode f=∑ u:D.probes, f u • principal k D u:=by
     have he:f=∑u:D.probes,f u • Pi.single u (1:ℂ):=by funext i;rw [Finset.sum_apply];simpa using (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by intro j _ hj;simp [Pi.single_eq_of_ne hj.symm]):(∑ u:D.probes,(f u • Pi.single u (1:ℂ)) i)=_).symm
     exact (congr_arg D.decode he).trans ((map_sum D.decode _ _).trans (Finset.sum_congr rfl (fun i _=>D.decode.map_smul _ _)))

private def cancel (e:Exterior C.book)(z:Points e.n):Option D.probes → ℂ
 | none=>1
 | some i=> -siteValue S e.letter _ (principal k D i) 0 z

private lemma subtracted (e:Exterior C.book)(z:Points e.n)(f:D.probes → ℂ)(x:ℂ):
    (∑ u:Option D.probes,cancel k D e z u * Option.elim u x f) = x-siteValue S e.letter k (D.decode f) 0 z:=by
       let L := Work.A01.frontRead (S.classTokens∘e.letter) (Points.cons 0 z) k
       rw [decode_eval k D]
       simp only [Fintype.sum_option,cancel,Option.elim,one_mul,siteValue,fixedValue,← Work.A01.front_eval,map_sum,map_smul]
       change _= _ - ∑ i:D.probes, f i * L (principal k D i)
       rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]; congr 1; exact Finset.sum_congr rfl fun i _=>by ring
private lemma combo_eval (e:Exterior C.book)(z:Points e.n)(y:E4): Local.combo (probes k D e) A B (cancel k D e z) (locs k D e z) y=missAt k D (kernelAnchor A B) e z y:=by
        let f(i:D.probes):=kernelAnchor A B i y (relative (i:Exterior C.book))
        calc _ = (∑u:Option D.probes,cancel k D e z u * Option.elim u (kernelAnchor A B e y z) f):= by
                    apply Finset.sum_congr rfl; intro i hi; cases i <;> dsimp only [kernelAnchor,anchoredValue,anchored,positions,add_zero,locs,probes,f,Option.elim] <;> rw [add_zero] <;> rfl
             _ = _:=subtracted k ..
private lemma silence (H:S.Hierarchy)(e:Exterior C.book)(z:Points e.n):Local.silent (probes k D e) S k (locs k D e z) (cancel k D e z):=by
       intro v
       rw [show (∑ i:Option D.probes,_) = (∑i:Option D.probes, cancel k D e z i * Option.elim i (siteValue S e.letter k v 0 z) (fun i=>response S k (i:Exterior C.book) v)) from ?_,subtracted k D e z,D.fixes v,sub_self]
       exact Finset.sum_congr rfl (fun i _=>by congr 1; cases i with
          | none=> rfl
          | some a=> exact site_orig S H.translations (a:Exterior C.book) k v H.laws.toSymmetric (fun _=>le_rfl))

include H
lemma anchor_miss : AtPrice (fun e y z=>missAt k D (kernelAnchor A B) e z y) ((k:ℝ) - massDeg A B+gain):=by
    intro e K hK hr
    let f:=locs k D e
    have hs(x)(hz:x∈f '' K)(i):Points.cons 0 (x i)∈conf _:= by
        obtain ⟨x,hx,rfl⟩:=hz
        cases i with
        | none=> exact hr x hx
        | some j=> exact relative_safe _
    obtain ⟨r,hR,ht⟩:=Local.pairSigned H.oriented (probes k D e) A B _ (hK.image (continuity_locs k D e)) hs H.aroma H.fees H.deriv H.seed.kernel H.seed.generic H.seed.copies H.seed.cutoff H.simple k
    have he := hK.bddAbove_image (f:=fun x:Points _ =>∑ u:Option D.probes, ‖cancel k D e x u‖) (continuousOn_of_forall_continuousAt (fun p hp=>?_))
    swap
    · apply tendsto_finsetSum _
      intro i hi; cases i with
      | none=>exact continuousAt_const
      | some i=> exact (((Local.once_tends e.letter p (hr p hp) (principal k D i) H.seed.kernel).comp_of_eq (continuous_id.prodMk continuous_const).continuousAt rfl).neg.norm)
    obtain ⟨C0,hc⟩:=he
    let C₁:=max 1 C0; have hc':0<C₁:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
    refine ⟨C₁,hc'.le,?_⟩
    filter_upwards [norm_eventually (E:=E4) r hR] with y ⟨hy₀,hy⟩ z hz
    let c:=cancel k D e z; let d(u:Option D.probes):ℂ:= c u / (C₁:ℝ)
    have hv:=ht (f z) (mem_image_of_mem f hz) d (?_) (?_) y hy₀ hy
    rotate_left
    · simp_rw [d,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc']; exact (Finset.sum_div ..).symm.le.trans ((div_le_one hc').2 ((hc (mem_image_of_mem _ hz)).trans (le_max_right ..)))
    · intro v; unfold d; simp_rw [div_mul_eq_mul_div, ← Finset.sum_div,show c=cancel k D e z from rfl,show f=locs k D e from rfl,silence k D H.seed.kernel e z v,zero_div]
    unfold Local.combo at hv; simp_rw [d,div_mul_eq_mul_div,← Finset.sum_div,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc'] at hv
    have ht : (-(B.fst:ℝ)-A.fst+k+1/64)=k-massDeg A B+gain:=by unfold massDeg gain;push_cast;ring
    rw [← ht,mul_comm]; exact (congr_arg (‖·‖) ((combo_eval k A B D e z y)).symm).le.trans ((div_le_iff₀ hc').1 hv)
end YM.MultipleContact.Two
