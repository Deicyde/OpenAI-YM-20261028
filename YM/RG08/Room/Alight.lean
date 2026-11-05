import YM.RG08.Room.Glass

/-! # Spare season / nonce elimination for Jacobian change. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Room
open Forms Glyph Cloud Finset Function MvPolynomial
open scoped PowerSeries BigOperators Topology Classical
variable {I:Type}[Fintype I]
namespace Haze
variable (H:Haze I)
abbrev Jot (I:Type):=Unit ⊕ I

def active {I:Type} : I↪Jot I:=⟨Sum.inr,Sum.inr_injective⟩
def lifted (H:Haze I):Haze (Jot I) where
 foam := H.foam.map active
 price := Sum.elim (fun _ _=>0) (fun i=>Sum.elim (fun _=>0) (H.price i))
 flipped i j:=by cases i <;> cases j <;> simp [H.flipped]
 dryL i j hi:=by
    cases i <;> cases j <;> try rfl
    rename_i i j; exact H.dryL i j (fun h=>hi (Finset.mem_map_of_mem active h))

abbrev tick :Jot I:=.inl ()
omit [Fintype I] in
lemma inactive : tick∉H.lifted.foam:=by simp [lifted,active,tick]

def noon (i:I):Port (Jot I):=rod (.inr i)
def dawn : Port I→ₐ[ℝ] Port (Jot I):=belt noon

private def traceL (i:I)(j:Jot I):ℝ:=if Sum.inr i=j then 1 else 0
omit [Fintype I] in
lemma guard : Scout H H.lifted noon traceL:=by
 constructor
 · intro i hi; have he: Sum.inr i ∈ H.lifted.foam:=mem_map_of_mem active hi
   simp [traceL,he,noon,ite_smul]
 · intro i hi; apply abroad_atom
   simpa [lifted,active] using hi
 intro i k hi hk
 simp only [traceL,mul_ite,mul_one,mul_zero];simp [lifted,active,hi,hk]

omit [Fintype I] in
lemma unguard : Injective (dawn (I:=I)):=by
 let t : Jot I→Port I:=Sum.elim (fun _=>0) rod
 intro a b h
 apply_fun belt t at h
 change ((belt t).comp (belt noon)) _=((belt t).comp (belt noon)) _ at h
 rw [switched,show (fun i=>belt t (noon i))=rod from funext (fun i=>belt_x ..),belt_id,belt_id] at h
 exact h
lemma fit_pin (i:I)(p:Port I):pin (.inr i) (dawn p)=dawn (pin i p):=by
 unfold dawn; rw [belt_chain,sum_eq_single i (by intro b _ hi; rw [noon,pins,if_neg (by simp [Ne.symm hi]),mul_zero]) (by simp)];rw [noon,pins,if_pos rfl,mul_one]
lemma freeze (p:Port I):pin tick (dawn p)=0:=by unfold dawn;rw [belt_chain];apply Finset.sum_eq_zero;intro i _;rw [noon,pins,if_neg (by simp [tick]),mul_zero]

-- clocks don't alter field CVs, adjoin identity on spare for determinant

def hoist (x:I→Port I):Jot I→Port (Jot I):=Sum.elim (fun _=>rod tick) (fun i=>dawn (x i))
omit [Fintype I] in
lemma hoist_chain (x:I→Port I)(p:Port I):belt (hoist x) (dawn p)=dawn (belt x p):=by
 change ((belt (hoist x)).comp (belt noon)) p=((belt noon).comp (belt x)) p
 rw [switched,switched,show (fun i=>belt (hoist x) (noon i))=(fun i=>dawn (x i)) from funext (fun i=>belt_x ..)];rfl
private def poem (Q:Inn I):Inn (Jot I):=rename Sum.inr Q
omit [Fintype I] in
private lemma dawn_light (Q:Inn I):dawn (liftInn Q)=liftInn (poem Q):=by
 unfold dawn;rw [belt_c]
 induction Q using MvPolynomial.induction_on with
 | C r=>unfold poem lug;rw [aeval_C,rename_C,PowerSeries.algebraMap_apply];rfl
 | add a b ha hb=>unfold poem at *;rw [_root_.map_add,_root_.map_add,_root_.map_add,ha,hb]
 | mul_X a i ih=>unfold poem at *;rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,ih,rename_X,lug,aeval_X];rfl

omit [Fintype I] in
lemma dawn_head {x:I→Port I}(h:Near x):Near (hoist x):=by
 rintro (u|i)
 · cases u;simp [tap,hoist,rod,tick,liftInn]
 change tap 0 (belt noon _)=_;rw [rim,h i,MvPolynomial.aeval_X];simp [noon,rod,tap,liftInn]

private lemma hoist_gate (x:I→Port I):gate (hoist x) = Matrix.fromBlocks (1:Matrix Unit Unit (Port (Jot I))) 0 0 (dawn.mapMatrix (gate x)):=by
 ext i j :1
 cases i <;> cases j
 · rename_i u r; cases u;cases r;change pin tick (rod (tick:Jot I))=(1 : Matrix Unit Unit (Port (Jot I))) () (); rw [pins,Matrix.one_apply];simp
 · rename_i u i; change pin (.inr i) (rod (tick:Jot I))=0; simp [pins,tick]
 · rename_i i u;cases u;change pin (tick) (dawn _)=0;rw [freeze]
 rename_i i j;exact fit_pin j (x i)
lemma hoist_det (x:I→Port I): (gate (hoist x)).det=dawn (gate x).det:=by rw [hoist_gate,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,one_mul, ← AlgHom.map_det]

/-- No spare variable version of Jacobian conservation. Use centered coordinates. Doesn't
assert positivity or nondegeneracy; consume centered precision-covariance equation. -/
theorem absorbed {P:I→I→ℝ}{Q:Inn I}{x:I→Port I}(hz:Near x)(ho:anchored H.foam x)(hb:H.Boil P Q)
    (F:Port I)(hu:tiny F): H.evolve x F Q=H.brew (rise F):=by
 let t:=H.lifted
 let y:=hoist x
 have h:anchored t.foam y:=by
   intro i hi; cases i with
   | inl u=>cases u;rfl
   | inr i=>change dawn (x i)=_; rw [ho i (by simpa [t,lifted,active] using hi),dawn,belt_x];rfl
 have he(i)(hi:i∈t.foam):pin tick (y i)=0:=by
    rcases i with u|i
    · cases u;exact False.elim (H.inactive hi)
    exact freeze (x _)
 have hd(i:I)(p:Inn I):pderiv (.inr i) (poem p)=poem (pderiv i p):=by
    have he:=fit_pin i (liftInn p)
    rw [dawn_light,pin_c,pin_c,dawn_light] at he
    have ht:=congrArg (tap 0) he;simpa [tap,liftInn] using ht
 have hb': t.Boil (Sum.elim (fun _ _=>0) (fun i=>Sum.elim (fun _=>0) (P i))) (poem Q):=by
    constructor
    · rintro (⟨⟩|i) hi j
      · exact False.elim (H.inactive hi)
      have hx:=hb.1 i (by simpa [lifted,active,t] using hi)
      cases j <;> simp [t,lifted,active,hx]
    rintro (⟨⟩|i) hi
    · exact False.elim (H.inactive hi)
    rw [hd,hb.2 i (by simpa [lifted,t,active] using hi)]
    simp [t,poem,lifted,active,_root_.map_smul]
 have ha':Near y:=dawn_head hz
 have hu':tiny (dawn F):=by unfold tiny at *;change tap 0 (belt noon F)=_; rw [rim]; unfold tap;rw [hu,map_zero]
 have hh:=still (H:=t) H.inactive ha' h he hb' (dawn F) (freeze F) (by rw [←dawn_light];exact freeze _) hu'
 apply unguard
 unfold evolve at *
 unfold y at hh; simp_rw [←dawn_light, hoist_chain] at hh -- y let
 simp only [dawn,←entrusted (guard H),_root_.map_mul,belt_rose _ (neartiny hz hu Q),belt_rose _ hu,map_add,map_sub]
 -- maybe names
 refine Eq.trans ?_ hh
 apply congrArg t.brew; apply congrArg₂ (·*·) rfl; 
 have hr:= (hoist_det x).symm
 rw [show (@instDecidableEqSum Unit I _ (Classical.decEq I))=(Classical.decEq (Jot I)) from Subsingleton.elim _ _] at hr;exact hr
