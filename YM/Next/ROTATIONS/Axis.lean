import YM.Axis.Matrix

/-!
# Outer analysis: genuine coordinate-axis spectral kernels

Both arbitrary clusters and point-like clusters are finite linear combinations of
strictly separated words. The correlation tested below is *antilinear* in the cluster
at the origin, **linear** in the cluster placed at `y`; we include ordinary conjugation
(not plane reflection) on the former. (The final real-kernel and arbitrary-quotient-label
identities do not put this conjugation into the local Ward maps.) Character projection acts
on offsets too. We guard collision values by zero; no integral uses them as a trace.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Outer
open Set Filter Function MeasureTheory Measure Matrix Complex Boundary Probe Row OS Word
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ComplexConjugate
variable {G : Gauge} {L : Register G} {S : Table L}

lemma act_comp (s t : Signed) (w : L.Word) : act s (act t w)=act (s*t) w := by
  simp only [act, List.map_map]
  congr 1
  funext p; rcases p with ⟨p,v⟩
  refine Prod.ext ?_ ?_
  · change Ortho.move _ (Ortho.move _ _) = _
    rw [← Ortho.move_mul,show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO s t]
  · cases v
    simp [Register.move]

lemma act_id (w : L.Word) : act 1 w=w := by
  unfold Word.act
  convert List.map_id w using 1
  congr 1
  funext p; rcases p with ⟨p,d,v⟩
  simp [Register.move, show (1 : Signed).ortho=1 from map_one Signed.inclusionO]

lemma act_conj (s : Signed) (w : L.Word) : act s (Word.conjugate w)=Word.conjugate (act s w) := by
  simp only [Word.conjugate,Word.act,List.map_map]
  congr 1
  funext p; rcases p with ⟨p,d,v⟩
  simp [Register.move, Register.conjugate]

lemma carried (s : Signed) (w : L.Word) (x : E4) : carry (act s w) (Ortho.move s.ortho x)=act s (carry w x) := by
  simp only [Word.act, carry,List.map_map]; congr 1
  funext p; rcases p with ⟨p,v⟩
  exact Prod.ext ((Ortho.motion _).map_add _ _).symm rfl

lemma distinct_act (s : Signed) (w : L.Word) : distinct (act s w) ↔ distinct w := by
  have imp (s : Signed) (w : L.Word) (h : distinct w) : distinct (act s w) := by
    rw [locations, show List.map Prod.fst (act s w) = List.map (Ortho.move s.ortho) (w.map Prod.fst) by simp [act,List.map_map]]
    exact (locations.mp h).map (Ortho.move_injective _)
  refine ⟨fun h => ?_,imp s w⟩
  simpa only [act_comp,inv_mul_cancel,act_id] using imp s⁻¹ (act s w) h

def rotate (s : Signed) : Core L ≃ Core L where
  toFun w := ⟨act s w.val,(distinct_act s _).mpr w.property⟩
  invFun w := ⟨act s⁻¹ w.val,(distinct_act _ _).mpr w.property⟩
  left_inv w := Subtype.ext (by simp [act_comp,act_id])
  right_inv w := Subtype.ext (by simp [act_comp,act_id])

def ink (s : Signed) : Weight L ≃ₗ[ℂ] Weight L := Finsupp.domLCongr (rotate s)
lemma ink_single (s : Signed) (w : Core L) (c : ℂ) : ink s (Finsupp.single w c)=Finsupp.single (rotate s w) c :=
  Finsupp.domLCongr_single ..

def signValue (b : Bool) : ℂ := if b then -1 else 1
lemma sign_real (b) : star (signValue b)=signValue b := by cases b <;> simp [signValue]
lemma sign_sq (b) : signValue b*signValue b=1 := by cases b <;> simp [signValue]

/-- True is odd. Reflection on the raw alphabet already (with its offsets).
Existence of eigen-combinations posing the stress probes will use character projection;
no assumption the chosen section of quotient fields preserves anything here. -/
def Own (A : Weight L) (a : Axis) (b : Bool) : Prop := ink (Signed.mirror a) A = signValue b • A

variable (S)

open scoped Classical in
def bare (v w : Core L) (y : E4) : ℂ :=
  let p := conjugate v.val.reverse ++ carry w.val y
  if distinct p then S.expect p else 0

def readsCluster (B A : Weight L) (y : E4) :=
  B.sum (fun v b => star b * A.sum (fun w a => a * bare S v w y))

lemma bare_turn (h : S.RealSpin) (s : Signed) (v w : Core L) (y : E4) :
    bare S (rotate s v) (rotate s w) (Ortho.move s.ortho y)=bare S v w y := by
  classical
  let p := conjugate v.val.reverse ++ carry w.val y
  have he : Word.conjugate (act s v.val).reverse ++ carry (act s w.val) (Ortho.move s.ortho y)=act s p := by
    rw [carried,show (act s _).reverse=act s v.val.reverse from List.map_reverse.symm,← act_conj]
    simp [Word.act,p,-List.map_reverse]
  change (if distinct _ then _ else _) = if distinct p then _ else _
  have he' : Word.conjugate ((rotate s v).val.reverse) ++ carry (rotate s w).val (Ortho.move s.ortho y)=act s p := he
  simp only [he', distinct_act]
  split_ifs with H
  · have hp : act s p = realize (L.move s ∘ tokens p) (Points.move s.ortho (positions p)) := by
      let f := fun x : L.Plant => (Ortho.move s.ortho x.1,L.move s x.2)
      have hf : (List.ofFn p.get).map f = List.ofFn (f ∘ p.get) := List.map_ofFn
      rw [List.ofFn_get] at hf
      exact hf
    rw [hp,Table.readAt]; exact h.mirror s H _
  · rfl

lemma reads_add_l (B C A : Weight L) (y) : readsCluster S (B+C) A y=readsCluster S B A y+readsCluster S C A y := by
  classical
  unfold readsCluster
  rw [Finsupp.sum_add_index']
  all_goals simp [add_mul]
lemma reads_add_r (B C A : Weight L) (y) : readsCluster S B (C+A) y=readsCluster S B C y+readsCluster S B A y := by
  classical
  unfold readsCluster
  simp [Finsupp.sum_add_index', Finsupp.sum_add, add_mul,mul_add]
lemma reads_smul_l (B A : Weight L) (c : ℂ) (y) : readsCluster S (c•B) A y = star c * readsCluster S B A y := by
  classical
  unfold readsCluster
  rw [Finsupp.sum_smul_index]; swap; · simp
  simp only [Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [star_mul,mul_comm (star _)]
  simp [mul_assoc]
lemma reads_smul_r (B A : Weight L) (c : ℂ) (y) : readsCluster S B (c•A) y = c * readsCluster S B A y := by
  classical
  have hx (v) : (c • A).sum (fun w a => a * bare S v w y) = c * A.sum (fun w a => a * bare S v w y) := by
    rw [Finsupp.sum_smul_index]; swap; · simp
    simp only [Finsupp.sum, Finset.mul_sum, mul_assoc]
  unfold readsCluster
  simp_rw [hx]
  simp only [Finsupp.sum,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => mul_left_comm _ _ _

lemma reads_ink_l (B A : Weight L) (s : Signed) (y : E4) :
    readsCluster S (ink s B) A y = B.sum (fun v b => star b * A.sum (fun w a => a * bare S (rotate s v) w y)) := by
  induction B using Finsupp.induction_linear with
  | zero => simp [readsCluster]
  | add p q hp hq => simp [reads_add_l,hp,hq,Finsupp.sum_add_index',add_mul]
  | single i z => simp [ink_single,readsCluster,Finsupp.sum_single_index]

lemma reads_turn (H : S.RealSpin) (s : Signed) (B A : Weight L) (y : E4) :
    readsCluster S (ink s B) (ink s A) (Ortho.move s.ortho y)=readsCluster S B A y := by
  induction A using Finsupp.induction_linear with
  | zero => simp [readsCluster]
  | add p q hp hq => simp only [map_add,reads_add_r,hp,hq]
  | single i z =>
    rw [ink_single, reads_ink_l]
    simp [readsCluster,bare_turn S H]

/-- Temporal parity works before any distribution extension. -/
lemma reads_mirror (H : S.RealSpin) (i : Axis) (B A : Weight L) (b a) (hb : Own B i b) (ha : Own A i a)
    (y : E4) : readsCluster S B A (Ortho.move (Signed.reflect i) y)=signValue b*(signValue a * readsCluster S B A y) := by
  have he := reads_turn S H (Signed.mirror i) B A y
  rw [show ink _ B=_ from hb, show ink _ A=_ from ha, reads_smul_l, reads_smul_r, sign_real] at he
  rw [← he]
  cases a <;> cases b <;> simp [signValue,Signed.reflect]

variable {S} {i : Axis}
variable (V : Chamber S i)

lemma moved_cross (x : Cross i) : V.flow.unit.translation x.val = V.flow.U x := by
  have hx : Semigroup.SEP i x.val=x := by
    apply Subtype.ext
    change x.val-x.val i • basis i=x.val
    rw [x.property,zero_smul,sub_zero]
  change (V.flow.edge (x.val i)).comp _=_
  rw [hx,x.property,V.flow.birth,ContinuousLinearMap.id_comp]

private lemma lifted (u : ℝ≥0) (w : Core L) (h : ∀ p∈w.val,0<p.1 i+(u:ℝ)) :
    Word.Positive (carry w.val ((u:ℝ) • basis i)) i := by
  refine ⟨still w.property _,fun x hx => ?_⟩
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  simpa using h p hp

lemma bare_pair (H : S.Homogeneous) (v w : Core L) (u t : ℝ≥0) (x : Cross i)
    (hv : ∀ p∈v.val,0<p.1 i+(u:ℝ)) (hw : ∀ p∈w.val,0<p.1 i+(u:ℝ)) :
    inner ℂ (bud V v (u:ℝ)) (V.flow.U x (V.flow.E t (bud V w (u:ℝ)))) =
      bare S (rotate (Signed.mirror i) v) w ((((u+u+t:ℝ≥0):ℝ)) • basis i+x.val) := by
  classical
  let s : E4 := (u:ℝ) • basis i
  let a : Future L i := ⟨carry v.val s,lifted u v hv⟩
  let b : Future L i := ⟨carry w.val s,lifted u w hw⟩
  rw [bud,bud, dif_pos a.property,dif_pos b.property]
  change inner ℂ (V.GNS.plant a) (V.flow.U x (V.flow.E t (V.GNS.plant b))) = _
  rw [← V.atBirth t b,← V.across,V.GNS.measure]
  let q := reflect a.val i ++ (over (travel b t) x).val
  let y : E4 := (((u+u+t:ℝ≥0):ℝ)) • basis i+x.val
  have he : reflect v.val i = Word.conjugate ((rotate (Signed.mirror i) v).val.reverse) := by
    change act _ (conjugate _) = conjugate (act _ _).reverse
    rw [act_conj]; simp only [Word.act,List.map_reverse]
  have hf : carry q s= conjugate ((rotate (Signed.mirror i) v).val.reverse) ++ carry w.val y := by
    have hr : Ortho.move (Signed.reflect i) s= -s := by
      ext j; by_cases hj : j=i <;> simp [hj,s]
    unfold q
    rw [distribute]
    dsimp only [over,travel,a,b]
    rw [refl_over,paths,hr,neg_add_cancel,rest,he]
    simp only [paths]
    congr 2
    simp only [y,s,NNReal.coe_add,add_smul]
    abel
  have hq : distinct q := twoSides a.property (over ..).property
  change S.expect q=if distinct _ then _ else _
  have hr : distinct (conjugate ((rotate (Signed.mirror i) v).val.reverse) ++ carry w.val y) := hf ▸ still hq s
  rw [if_pos hr]
  exact (invariance H hq s).symm.trans (congr_arg _ hf)

lemma placed (H : S.Homogeneous) (B A : Weight L) (u t : ℝ≥0) (x : Cross i)
    (hb : Lowered i B u) (ha : Lowered i A u) :
    V.flow.J x.val (root V B u) (root V A u) (I * ↑(t:ℝ)) =
    readsCluster S (ink (Signed.mirror i) B) A ((((u+u+t:ℝ≥0):ℝ)) • basis i+x.val) := by
  classical
  unfold Semigroup.J OS.Semigroup.ray
  rw [moved_cross,show (I * ↑(t:ℝ)).re=0 by simp, show (I * ↑(t:ℝ)).im.toNNReal=t by simp,
    V.flow.birth,ContinuousLinearMap.id_apply, reads_ink_l]
  unfold root
  simp only [Finsupp.sum,_root_.map_sum,map_smul,sum_inner,inner_sum, Finset.mul_sum,inner_smul_left,inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => ?_
  rw [bare_pair V H v w u t x (hb v hv) (ha w hw)]
  exact mul_left_comm .. 

def propagator (i : Axis) (t : ℝ) (x : E4) (p : E4) : ℂ :=
  (Real.exp (-t*p i):ℝ) * plane p x

lemma packed (t u : ℝ≥0) (x : E4) : pack x u i (I*↑(t:ℝ))= propagator i (u+u+t:ℝ≥0) x := by
  funext p
  dsimp only [pack,propagator,Paley.weight]
  rw [show ↑(p i)*(I*↑(t:ℝ))*I=((-(t:ℝ)*p i:ℝ):ℂ) by
    push_cast; ring_nf; simp [I_sq]]
  rw [← Complex.ofReal_exp]
  change (Real.exp _ : ℝ) • (_ : ℂ) = _
  simp only [NNReal.coe_add, neg_add, add_mul,Real.exp_add,Complex.real_smul,Complex.ofReal_mul]
  ring

lemma axis_rep (H : S.Homogeneous) (B A : Weight L) (b : Bool) (hh : Own B i b) (u : ℝ≥0)
    (hb : Lowered i B u) (ha : Lowered i A u) (s : ℝ) (hs : u+ (u:ℝ) ≤ s) (x : Cross i) :
    fits V B A (propagator i s x.val) ∧ signValue b * readsCluster S B A (s • basis i+x.val) = cross V B A (propagator i s x.val) := by
  let k : ℝ≥0 := ⟨s-(u+ (u:ℝ)),sub_nonneg.mpr hs⟩
  have he := reply V x.val u (I*↑(k:ℝ)) (by simp [Paley.high]) B A hb ha
  rw [packed, placed V H B A u k x hb ha, hh, reads_smul_l,sign_real,show ((u+u+k:ℝ≥0):ℝ)=s by simp only [NNReal.coe_add]; exact add_sub_cancel .. ] at he
  exact he

lemma axis_auto (H : S.Homogeneous) (A : Weight L) (b : Bool) (hh : Own A i b) (u : ℝ≥0)
    (ha : Lowered i A u) (s : ℝ) (hs : u+ (u:ℝ) ≤ s) (x : Cross i) :
    Integrable (propagator i s x.val) (ν V A) ∧
    signValue b * readsCluster S A A (s • basis i+x.val) = ∫ p, propagator i s x.val p ∂ν V A := by
  let k : ℝ≥0 := ⟨s-(u+ (u:ℝ)),sub_nonneg.mpr hs⟩
  have he := reads V x.val u (I*↑(k:ℝ)) (by simp [Paley.high]) A ha
  -- reads_* also equality at edge
  simp_rw [show ∀ p, pack x.val u i (I * ↑(k:ℝ)) p = propagator i ((u+u+k:ℝ≥0):ℝ) x.val p from
    congr_fun (packed k u x.val)] at he
  rw [placed V H A A u k x ha ha,hh,reads_smul_l,sign_real,packed,show ((u+u+k:ℝ≥0):ℝ)=s by simp only [NNReal.coe_add]; exact add_sub_cancel .. ] at he
  exact he
end YM.Outer
