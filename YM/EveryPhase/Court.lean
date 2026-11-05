import YM.EveryPhase.Decree

/-! # Matrix elements through compact exterior approximation -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table
open Next.BOUNDARY.Descent
open scoped Topology BigOperators
variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {F : Waves S} {H : S.RealSpin} {n : ℕ}

lemma dress (f : Fin n → Test4) (t : Test4) (j : Fin (n+1)) :
    Joint.materialize _ (hole j f t)=cloth (Joint.materialize n f) j t := by
  ext1 x
  obtain ⟨⟨x,y⟩,rfl⟩ := (chairs j).surjective x
  change Joint.materialize _ _ (seat j x y)=cloth _ _ _ (seat j x y)
  rw [clothes,Joint.material_at,Joint.material_at,Fin.prod_univ_succAbove _ j]; simp [mul_comm]

lemma ticket (f : Fin n → Test4) (i : Fin n) {x : Points n} (hx : x∈tsupport (Joint.materialize _ f)) :
    x i∈tsupport (f i) := by
  -- Work.C27 coordinate_tsupport
  have hs : tsupport (Joint.materialize n f) ⊆ (fun x : Points n => x i) ⁻¹' tsupport (f i) := by
    refine closure_minimal ?_ ((isClosed_tsupport _).preimage (by fun_prop))
    intro x hx
    apply subset_tsupport
    intro h
    apply hx; exact (Joint.material_at f x).trans (Finset.prod_eq_zero (Finset.mem_univ i) h)
  exact hs hx
lemma cost (f : Fin n → Test4) (h : ∀ i, HasCompactSupport ⇑(f i)) : HasCompactSupport ⇑(Joint.materialize _ f) := by
  let k : Fin n→ Set E4 := fun i => tsupport (f i)
  have hk := isCompact_univ_pi (s:=k) h
  apply IsCompact.of_isClosed_subset (hk.image (show Continuous (points (n:=n)) by unfold points; fun_prop)) (isClosed_tsupport _)
  intro x hx; exact ⟨x.ofLp, fun i _ => ticket f i hx, rfl⟩

lemma turn_effect (f : Fin n → Test4) (t : Test4) (j : Fin (n+1)) (K : Killing) (b : Axis) :
    effect K b (PiLp.proj 2 _ j) (Joint.materialize _ (hole j f t))=Joint.materialize _ (hole j f (touch K b t)) := by
  rw [dress,dress]
  ext1 x
  rw [effect_at]; obtain ⟨⟨x,y⟩,rfl⟩ := (chairs j).surjective x
  change (K.realV (seat j x y j) b:ℂ)*cloth (Joint.materialize n f) j t (seat j x y)=cloth _ _ _ (seat j x y)
  simp only [seat_seat,clothes,touch_at]; ring

lemma inserting {A : Type*} (f : Fin n → A) (j : Fin (n+1)) (v : A) :
    List.ofFn (hole j f v)=(List.ofFn f).insertIdx j.val v := by
  induction n with
  | zero => rw [Fin.eq_zero j]; simp [hole]
  | succ n IH =>
    induction j using Fin.cases with
    | zero => simp [hole]
    | succ i =>
      have he : f=Fin.cons (f 0) (Fin.tail f) := by funext i; refine Fin.cases ?_ ?_ i <;> simp [Fin.tail]
      calc List.ofFn (hole i.succ f v) = List.ofFn (hole i.succ (Fin.cons (f 0) (Fin.tail f)) v) := by nth_rw 1 [he]
           _ = f 0 :: List.ofFn (hole i (Fin.tail f) v) := by rw [hole, Fin.insertNth_succ_cons,List.ofFn_cons]; rfl
           _ = _ := by rw [IH, List.ofFn_succ]; rfl
lemma introduce {A : Type*} (a b : List A) (v : A) : (a++b).insertIdx a.length v=a++v::b := by
  induction a with
  | nil => simp
  | cons t a ih => rw [List.cons_append,List.length_cons,List.insertIdx_succ_cons, ih,List.cons_append]
lemma two_more {A : Type*} (a b : List A) (v w : A) : (a++v::b).insertIdx (a.length+1) w=a++v::w::b := by
  simpa using introduce (a++[v]) b w

lemma adds_tensor (u : Fin n → S.Union) (f : Fin n → Test4) (j : Fin (n+1)) (a : Letter S) :
    tensorWord (hole j u a.1) (hole j f a.2)=(tensorWord u f).insertIdx j.val a := by
  rw [show tensorWord u f = List.ofFn (fun i => (u i,f i)) from rfl,← inserting]; unfold tensorWord; congr 1
  funext k; refine Fin.succAboveCases j ?_ ?_ k <;> simp
lemma tensor_read (W : Surface S) (u : Fin n → S.Union) (f : Fin n → Test4) :
    W.expect (tensorWord u f)=W.W n u (Joint.materialize n f) := by rw [tensorWord,Work.C29.expectOfFn]; rfl

def shells (W : Surface S) (R : S.Rotation) (P : DiffPlan S) (T : S.Stress) (K : Killing)
    (f : Probe ℝ) (g : Probe Space3) (x : S.Tag) (m : Test4) (a b : Sentence S) : Prop :=
  let ℓ : Letter S := (S.pin x.1 x.2,m)
  let r : Axis → Letter S := fun i => (S.pin 4 (T timeAxis i), touch K i (pincushion g f))
  (∑ i : Axis, zeta i*W.expect (a++ℓ::r i::b)) - (∑ i : Axis, zeta i*W.expect (a++r i::ℓ::b)) =
    W.expect (a++(S.pin x.1 (rankAction R x.1 K.V x.2),m)::b)+∑ i : Axis,
      zeta i* W.expect (a++(S.pin (x.1+1) (P.deriv x.1 i x.2),touch K i m)::b)
lemma compact_shells (K : Killing) (T : S.Stress) (B : S.Tag) (R : S.Rotation) (w : Prospect F Z U P H T)
    (h : StressLaws U T P.deriv R.lie) (ha : Gallery W Z) (m : Test4) (hm : HasCompactSupport ⇑m)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r) (f : Probe ℝ) (hf : HasCompactSupport ⇑f)
    (hu : (∫ x, f x)=1) (hk : ∀ x∈tsupport m, Jury g f x)
    (a b : Sentence S) (hb : ∀ i ∈ a++b, HasCompactSupport ⇑i.2) : shells W R P T K f g B m a b := by
  let e := a++b
  let n := e.length
  let k : Fin (n+1) := ⟨a.length,by simp [n,e]⟩
  let u := fun i => (e.get i).1
  let l := fun i => (e.get i).2
  let M := Joint.materialize (n+1) (hole k l m)
  have hM : HasCompactSupport ⇑M := by
    apply cost; intro i; refine Fin.succAboveCases k ?_ ?_ i
    · simp [hm]
    intro j; rw [hole_next]; exact hb _ (List.get_mem ..)
  choose d v hv using (fun i => P.covered w.hs w.hi (u i))
  let V : Fin n → S.Tag := fun i => ⟨d i, v i⟩
  have he : tensorWord u l=e := by simp [tensorWord,u,l]
  have hi (t : S.Tag) : Bid.ink (hole k V t)=hole k u (S.pin t.1 t.2) := by
    rw [ink_hole,show Bid.ink V=u by funext i; exact hv i] -- orientation
  have hv (t : Letter S) : tensorWord (hole k u t.1) (hole k l t.2)=a++t::b := (adds_tensor u l k t).trans (by rw [he]; exact introduce a b _)
  have hz (t : S.Tag) (f : Test4) : W.W (n+1) (Bid.ink (hole k V t)) (Joint.materialize _ (hole k l f))=
      W.expect (a++(S.pin t.1 t.2,f)::b) := by rw [hi,← tensor_read W,hv (S.pin t.1 t.2,f)] -- rw synth?
  let p : Letter S := (S.pin B.1 B.2,m)
  let u := Bid.ink (hole k V B)
  have hh : tensorWord u (hole k l m)=a++p::b := by unfold u; rw [hi]; exact hv p
  have hH (i : Fin (n+2)) (r : Letter S) :
      W.W (n+2) (hole i u r.1) (cloth M i r.2)= W.expect ((a++p::b).insertIdx i.val r) := by
    unfold M; rw [← dress,← tensor_read, adds_tensor u _ i r, hh]
  let r (i : Axis) : Letter S := (S.pin 4 (T timeAxis i), touch K i (pincushion g f))
  have h₁ (i : Axis) : W.W (n+2) (hole k.succ u (r i).1) (cloth M k.succ (r i).2)=W.expect (a++p::r i::b) := by
    rw [hH k.succ (r i),show k.succ.val=a.length+1 from rfl,two_more]
  have h₂ (i : Axis) : W.W (n+2) (hole k.castSucc u (r i).1) (cloth M k.castSucc (r i).2)=W.expect (a++r i::p::b) := by
    rw [hH k.castSucc (r i),show k.castSucc.val=a.length from rfl,introduce]
  have hV : stamp W K T u k.succ M g f-stamp W K T u k.castSucc M g f=receives W K R P V k B M := by
    rw [verdict K T V k B R w h M hM g hg hr f hf ha ?_,hu,mul_one]
    intro x h; apply hk
    have hx := ticket (hole k l m) k h; rwa [hole_self] at hx
  change (∑ i : Axis, zeta i*W.W (n+2) (hole k.succ u (r i).1) (cloth M k.succ (r i).2))-
    (∑ i : Axis, zeta i*W.W (n+2) (hole k.castSucc u (r i).1) (cloth M k.castSucc (r i).2))= _ at hV
  simp_rw [h₁,h₂] at hV; unfold receives M at hV; simp_rw [turn_effect,hz] at hV; exact hV

-- test continuity using joint materialization. No domain assertion involving compact test vectors as a graph core.
def shave (a : Sentence S) (k : ℕ) := tensorWord (fun i => (a.get i).1) (fun i => cap k (a.get i).2)
lemma widespread (a b r : Sentence S) (W : Surface S) : Tendsto (fun k => W.expect (shave a k ++ (r ++ shave b k))) atTop
    (𝓝 (W.expect (a++ (r++b)))) := by
  let v (t : Sentence S) : Fin t.length→S.Union := fun i => (t.get i).1
  let f (t : Sentence S) := fun i => (t.get i).2
  have he (t : Sentence S) : t=tensorWord (v t) (f t) := by simp [tensorWord,v,f]
  let n := a.length+(r.length+b.length)
  let V : Fin n → S.Union := Fin.append (v a) (Fin.append (v r) (v b))
  have hh {n m : ℕ} (u : Fin n → S.Union) (v : Fin m → S.Union) (f : Fin n → Test4) (g : Fin m → Test4) :
      tensorWord u f++tensorWord v g=tensorWord (Fin.append u v) (Fin.append f g) := by
    unfold tensorWord; rw [← List.ofFn_fin_append]; congr 1; funext i; refine Fin.addCases ?_ ?_ i <;> simp
  let A := Fin.append (f a) (Fin.append (f r) (f b))
  let p (k : ℕ) : Fin n → Test4 := Fin.append (fun i => cap k (f a i)) (Fin.append (f r) (fun i => cap k (f b i)))
  have hp : Tendsto p atTop (𝓝 A) := by
    apply tendsto_pi_nhds.mpr; intro i; refine Fin.addCases ?_ ?_ i <;> intro i
    · simp [p,A]; exact persistent _
    refine Fin.addCases ?_ ?_ i <;> intro i
    · simp [p,A]
    simp [p,A]; exact persistent _
  have hz (k) : shave a k++(r++ shave b k)=tensorWord V (p k) := calc
    _ = shave a k ++ (tensorWord (v r) (f r) ++ shave b k) := congr_arg (fun x => shave a k++(x++shave b k)) (he r)
    _ = _ := by rw [shave,shave,hh,hh]
  have h : a++ (r++b)=tensorWord V A := Eq.trans (congr_arg₂ (fun p q => p ++ q) (he a) (congr_arg₂ (fun p q => p ++ q) (he r) (he b)))
    (by rw [hh,hh])
  simp_rw [hz,h,tensor_read]
  exact (((W.W _ V).continuous.comp (Joint.jointCont n)).tendsto _).comp hp

lemma Schwartz_shells (K : Killing) (T : S.Stress) (B : S.Tag) (R : S.Rotation) (w : Prospect F Z U P H T)
    (h : StressLaws U T P.deriv R.lie) (ha : Gallery W Z) (m : Test4) (hm : HasCompactSupport ⇑m)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r) (f : Probe ℝ) (hf : HasCompactSupport ⇑f)
    (hu : (∫ x, f x)=1) (hk : ∀ x∈tsupport m, Jury g f x)
    (a b : Sentence S) : shells W R P T K f g B m a b := by
  let x : Letter S := (S.pin B.1 B.2,m)
  let r : Axis → Letter S := fun i => (S.pin 4 (T timeAxis i),touch K i (pincushion g f))
  let y : Letter S := (S.pin B.1 (rankAction R B.1 K.V B.2), m)
  let p : Axis → Letter S := fun i => (S.pin (B.1+1) (P.deriv B.1 i B.2), touch K i m)
  have hw (f : Axis→ Sentence S) := tendsto_finsetSum Finset.univ (fun i _ => (widespread a b (f i) W).const_mul (zeta i))
  apply tendsto_nhds_unique_of_eventuallyEq ((hw (fun i => [x,r i])).sub (hw (fun i => [r i,x])))
    ((widespread a b [y] W).add (hw (fun i => [p i])))
  filter_upwards with k
  have hh (v : Sentence S) : ∀ i ∈ shave v k, HasCompactSupport ⇑i.2 := by
    intro i hi; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi; exact finite_cap _
  exact compact_shells K T B R w h ha m hm g hg hr f hf hu hk (shave a k) (shave b k) (fun i hi =>
    (List.mem_append.mp hi).elim (hh a i) (hh b i))
end YM.EveryPhase.Stress
