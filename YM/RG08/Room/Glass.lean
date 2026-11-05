import YM.RG08.Room.Time
import YM.RG08.Room.Scout

/-! # Attach dummy clocks & complete the nonlinear near-id Jacobian. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Forms Glyph Cloud Finset Function MvPolynomial
open scoped PowerSeries BigOperators Topology Classical
variable {I:Type}{s:I}
namespace Haze
variable {H:Haze I}

def snag (s:I)(r:ℝ)(i:I):Port I:=if i=s then algebraMap ℝ (Port I) r else rod i
lemma tripped (H:Haze I)(r:ℝ)(hs:s∉H.foam):Scout H H (snag s r) (fun i j=>if i=j then 1 else 0):=by
 constructor
 · intro i hi; have he:i≠s:=by rintro rfl;exact hs hi
   simp [snag,he,ite_smul,hi]
 · intro i hi
   unfold snag;split_ifs
   · intro j _;apply Derivation.map_algebraMap
   exact abroad_atom hi
 intro i k hi hk; simp [mul_ite,sum_ite_eq,hi,hk]

lemma clockstop (s:I)(r:ℝ){f:Port I}(h:pin s f=0):belt (snag s r) f=f:=by
 have hp:Abroad ({s}:Finset I) f:=fun i hi=>by rw [mem_singleton] at hi; simpa [hi]
 rw [abroad_belt hp (y:=rod) (by simpa [snag] using (show ∀ i:I,i≠s→snag s r i=rod i from fun i hi=>if_neg hi)),belt_id]

def slides (s:I)(x:I→Port I)(i:I):=rod i+rod s*(x i-rod i)
lemma skating {x:I→Port I}(h:anchored H.foam x)(s:I):anchored H.foam (slides s x):=fun i hi=>by simp [slides,h i hi]
lemma skating0 (s:I){x:I→Port I}(h:Near x):Near (slides s x):=by
  intro i; unfold tap; rw [PowerSeries.coeff_zero_eq_constantCoeff];have he(i:I):PowerSeries.constantCoeff (x i)=MvPolynomial.X i:=by rw [←PowerSeries.coeff_zero_eq_constantCoeff]; exact h i
  simp [slides,rod,liftInn,he]
lemma clockslide (s:I){x:I→Port I}(ha:anchored H.foam x)(h:∀ i∈H.foam,pin s (x i)=0)(hs:s∉H.foam)(r:ℝ)(i:I):
    belt (snag s r) (slides s x i) = if i=s then snag s r s else rod i + algebraMap ℝ (Port I) r*(x i-rod i):=by
 split_ifs with ht
 · rw [ht,skating ha s s hs,belt_x]
 have hp : pin s (x i) = 0 := by
   by_cases hi : i ∈ H.foam
   · exact h i hi
   · rw [ha i hi, pins, if_neg (Ne.symm ht)]
 simp only [slides, map_add, _root_.map_mul, map_sub, belt_x, clockstop s r hp, snag, if_neg ht, if_true]

variable [Fintype I]

lemma clockpin (s i:I)(hi:i≠s)(r:ℝ)(f:Port I): pin i (belt (snag s r) f)=belt (snag s r) (pin i f):=by
 rw [belt_chain,Finset.sum_eq_single i]
 · rw [snag,if_neg hi,pins,if_pos rfl,mul_one]
 · intro j _ hj
   unfold snag;split_ifs
   · rw [Derivation.map_algebraMap, mul_zero]
   rw [pins,if_neg (Ne.symm hj),mul_zero]
 simp

/- equal determinant if the possibly empty s row is the identity row, regardless entries
in column s. -/
private lemma axis_eq {R:Type*}[CommRing R](x y:Matrix I I R)(s:I)(he:∀ i j,j≠s→x i j=y i j)
    (hx:∀ j,x s j=if j=s then 1 else 0)(hy:∀ j,y s j=if j=s then 1 else 0):x.det=y.det:=by
 rw [Matrix.det_apply,Matrix.det_apply];apply sum_congr rfl;intro k _; congr 1
 by_cases h:k s=s
 · apply prod_congr rfl; intro i _; rcases eq_or_ne i s with hi|hi
   · simp [hi,h,hx,hy]
   rw [he _ i hi]
 have hp:k.symm s≠ s:=fun h'=>h (by nth_rw 1 [←h']; exact k.apply_symm_apply _)
 rw [Finset.prod_eq_zero (Finset.mem_univ (k.symm s)) (by simp [hx,hp]), Finset.prod_eq_zero (Finset.mem_univ (k.symm s)) (by simp [hy,hp])]

set_option maxHeartbeats 400000 in
lemma clockgate (s:I)(r:ℝ){x y:I→Port I}(hs:x s=rod s)(hs':y s=rod s)(he:∀ i:I,i≠s→belt (snag s r) (x i)=y i):
    belt (snag s r) (gate x).det=(gate y).det:=by
 rw [AlgHom.map_det];apply axis_eq _ _ s
 · intro i j hj;change belt _ (pin j (x i))=pin j (y i);rcases eq_or_ne i s with hi|hi
   · subst i;rw [hs,hs',pins,if_neg hj,map_zero]
   rw [←clockpin _ _ hj,he i hi]
 · intro j;change belt _ (pin j _)=_;rw [hs,pins];split_ifs <;> simp
 intro j;change pin j (y s)=_;rw [hs',pins]

omit [Fintype I] in
lemma clockbelt (s:I)(r:ℝ){x y:I→Port I}(he:∀ i:I,i≠s→belt (snag s r) (x i)=y i)(p:Port I)(h:pin s p=0):
    belt (snag s r) (belt x p)=belt y p:=by
 change ((belt (snag s r)).comp (belt x)) p=(belt y) p
 rw [switched]; exact abroad_belt (W:={s}) (f:=p) (fun i hi=>by rw [Finset.mem_singleton.mp hi];exact h) (by simpa)

def evolve (H:Haze I)(x:I→Port I)(F:Port I)(Q:Inn I):Port I:=H.brew (rise (belt x F + belt x (liftInn Q) - liftInn Q)*(gate x).det)

omit [Fintype I] in
lemma neartiny {x:I→Port I}(h:Near x){f:Port I}(hf:tiny f)(q:Inn I):tiny (belt x f + belt x (liftInn q)-liftInn q):=by
    unfold tiny at *;rw [map_sub,map_add];change tap 0 (belt x f)+tap 0 (belt x (liftInn q))-_=_
    simp_rw [rim,show (fun i=>tap 0 (x i))=(fun i=>MvPolynomial.X (R:=ℝ) i) from funext h];simp [tap,hf]

lemma clockeon (H:Haze I){s:I}(r:ℝ){x y:I→Port I}(hs:s∉H.foam)(h:anchored H.foam x)(h':anchored H.foam y)(ht:Near x)(he:∀ i:I,i≠s→belt (snag s r) (x i)=y i)(p:Port I)(q:Inn I)
    (hp:tiny p)(hi:pin s p=0)(hj:pin s (liftInn q)=0):
    belt (snag s r) (evolve H x p q)=evolve H y p q:=by
  unfold evolve; rw [←Haze.entrusted (H.tripped _ hs),_root_.map_mul,clockgate _ _ (h s hs) (h' s hs) he,belt_rose _ (neartiny ht hp q),map_sub,map_add,clockstop _ _ hj,clockbelt _ _ he _ hi,clockbelt _ _ he _ hj]

/-- **Compare output before log** under a near-identity nonlinear coordinate change in g,
provided negative heat exponent and full finite Jacobian included. Needs spare variable s not used
in F,Q or transform. A canonical one is provided by adjoining and lifting all kernels. -/
theorem still {s:I}{P:I→I→ℝ}{Q:Inn I}{x:I→Port I}
    (hs:s∉H.foam)(hz:Near x)(ho:anchored H.foam x)(he:∀ i∈H.foam,pin s (x i)=0)(hb:H.Boil P Q)
    (F:Port I)(hf:pin s F=0)(hq:pin s (liftInn Q)=0) (hu:tiny F):
    H.evolve x F Q=H.brew (rise F):=by
  let p:=slides s x
  have ht : pin s (H.evolve p F Q)=0:= H.bottle hs (skating0 s hz) (skating ho s) hb F hf hq hu
  have he':∀ i,i≠s → belt (snag s 1) (p i)=x i:=fun i hi=>by simp only [p,clockslide s ho he hs,hi,↓reduceIte,_root_.map_one,one_mul];abel
  have hf':∀ i,i≠s → belt (snag s 0) (p i)=rod i:=fun i hi=>by simp only [p,clockslide s ho he hs,hi,↓reduceIte,_root_.map_zero,zero_mul,add_zero]
  have hx:=clockeon H 1 hs (skating ho s) ho (skating0 s hz) he' F Q hu hf hq
  rw [←hx,clockstop s 1 ht,←clockstop s 0 ht,clockeon H 0 hs (skating ho s) (y:=rod) (fun _ _=>rfl) (skating0 s hz) hf' F Q hu hf hq]
  unfold evolve; rw [belt_id,belt_id,add_sub_cancel_right]
  have hh : gate (rod (I:=I))=1:=by
    ext i j :1;change pin j _=_; rw [pins,Matrix.one_apply];simp [eq_comm]
  rw [hh,Matrix.det_one,mul_one]
end Haze
end YM.RG08.Room
