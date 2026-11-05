import YM.RG08.Gaussian.Report

/-!
# Return gauges and metric rate

Strong stability of both *unmodified* prescriptions `pink,blue` from that
of the link Hessian. Need more than just proportionality at zero; diagonal
catches ALL the blades. We use real Laurent axis prices so any downstream
rough division or path lifts are charged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Stationary
open scoped Topology BigOperators
variable {j n : ℕ} {k : ℝ}

lemma heart_h (hk : 0 < k) (hj : 4 ≤ j) (v : Train j) : Whole (pink k v) ∧ Whole (blue k v) :=
  ⟨(heart_saves _ hk hj (id : Train j → _)).1.whole v,(heart_saves _ hk hj (id : Train j → _)).2.whole v⟩
lemma heart_see (hk : 0 < k) (hj : 4 ≤ j) (v : Train j) {p} (hp : p∈baseCube) :
    (pink k v).read p=pulse k v p ∧ (blue k v).read p=vault k v p :=
    ⟨(heart_true _ hk hj v).1.echo p hp,(heart_true _ hk hj v).2.echo p hp⟩
lemma rotor_h (hk : 0 < k) (hj : 4 ≤ j) (v : Train j) {p} (hp : p∈baseCube) :
    (hessian (pink k v)).read p=rotor 1 k v p := by
  unfold hessian
  rw [(((Whole.boundary _).flipped).prod (heart_h hk hj v).1).read (Whole.boundary _) hp.1,
      ((Whole.boundary _).flipped).read (heart_h hk hj v).1 hp.1, (heart_see hk hj v hp).1,
      read_opposite _ hp.1, Exterior.reading,rotor,mirage_herm 1 _ hp.1,signal_unit]

lemma knuckle (v : Train j) (p : Momentum) (s : PlaqAxes) :
    rotor 1 k v p (coord s.val.1) (coord s.val.2)= - (q p s.val.1*q (-p) s.val.2*pulse k v p (plaquette s) (plaquette s)) := by
  let a:=s.val.1; let b:=s.val.2; let u:=v.bend k p; let f:=fun i=>(v.bulb k p i)⁻¹
  have he : coord a≠coord b := (coord_iff a b).not.mpr s.property.ne
  change rotor 1 k v p (coord a) (coord b)=-_
  unfold rotor pulse mirage; rw [signal_unit,signal_unit,Matrix.mul_smul,Matrix.smul_mul]
  rw [show (symbol 1 (-p)).transpose*mask 2 f*symbol 1 p=_ from blade_price (Exterior.q (-p)) (Exterior.q p) f]
  rw [Matrix.smul_apply,Matrix.sub_apply,Matrix.smul_apply]
  have hf : mask 1 f (coord a) (coord b)=0 := by rw [mask_value,if_neg he]
  rw [hf,smul_zero,zero_sub,smul_neg,neg_inj]
  let L : Frequency 1 0 := symbol 0 p; let R : Frequency 1 0 := symbol 0 (-p)
  have hz (t):inventory (coord t) f=f t := by simp [inventory,coord]
  change u⁻¹ * ( (diagonal (fun i : TypeFace 1=> inventory i f)*L*R.transpose*diagonal (fun i : TypeFace 1=> inventory i f)) : Matrix (TypeFace 1) (TypeFace 1) ℂ) (coord a) (coord b)= _
  rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_eq_single vac, diagonal_mul,transpose_apply,hz,hz,
      show L _ _=_ from sym_one p a, show R _ _=_ from sym_one _ b]; swap
  · exact fun i _ hi => False.elim (hi (vac_only i))
  · simp only [Matrix.smul_apply,smul_eq_mul]
    change _=q p a*q (-p) b*(u⁻¹*diagonal (fun i : TypeFace 2=> inventory i f) (plaquette s) (plaquette s))
    rw [diagonal_apply_eq,inventory]
    change _=q p a*q (-p) b*(u⁻¹*∏ t∈({a,b}: Finset Axis), f t)
    rw [Finset.prod_insert (by simpa using (show a≠b from s.property.ne)),Finset.prod_singleton]; ring
  all_goals first | exact fun i _ hi => False.elim (hi (vac_only i)) | simp

private lemma coax {A B : Row Unit Unit} {σ x} (hs : 0<σ) (h : A.strip σ x) (hb : Whole B) (s : Axis)
    (ht : ∀ p ∈ baseCube,RRead (A () ()) p = q p s*RRead (B () ()) p) : B.strip (σ/2) ((σ/2)⁻¹*x) := by
  have hA : Whole A := ⟨_,_,hs,h⟩
  have hz : Whole (dashAxis s A) := dash_whole hA s
  have heq : dashAxis s A=B := by
    apply bank_injective hz.safe hb.safe
    apply Whole.eq_on hz hb
    intro p hp
    apply renew_q (Row.read (dashAxis s A)) (Row.read B) s (fun _ hv=> read_here _ hz hv)
      (fun _ hv => read_here _ hb hv) _ p hp
    intro p hp hr
    ext i y; cases i; cases y
    apply mul_left_cancel₀ hr
    have he := read_part hA s hp.1
    change q p s * (dashAxis s A).read p () ()=_
    have hq : q (update p s 0) s=0 := by simp [q]
    change q p s • (dashAxis s A).read p () ()=q p s*RRead (B () ()) p
    rw [← ht p hp, ← Matrix.smul_apply (r:=q p s),he,Matrix.sub_apply,show A.read (update p s 0) () ()=0 from
        (ht _ (bank_blank hp s)).trans (by rw [hq,zero_mul]),sub_zero]; rfl
  rw [← heq]; intro i j
  exact (dividend σ hs s).released (by positivity) (h i j) (by positivity)

private def sampleRow {α β : Type} (V : Row α β) (i : α) (j : β) : Row Unit Unit := fun _ _ => V i j
private lemma sample_whole {α β : Type} {V : Row α β} (h : Whole V) (i : α) (j : β) : Whole (sampleRow V i j) := by
  obtain ⟨σ,c,hσ,H⟩ := h; exact ⟨_,_,hσ,fun _ _=> H i j⟩

lemma sight_hues (hk : 0 < k) (hj : 4 ≤ j) {σ : ℝ} (hs : 0<σ) (v w : Train j) {X : ℝ}
    (hX : 0 ≤ X) (h : (minusRows (hessian (pink k v)) (hessian (pink k w))).strip σ X) :
    (minusRows (pink k v) (pink k w)).strip (σ/2/2) ((σ/2/2)⁻¹*((σ/2)⁻¹*X)) := by
  intro i t
  let U:=pink k v; let V:=pink k w; let F:=minusRows U V
  have hu : Whole U := (heart_h hk hj v).1; have hv : Whole V := (heart_h hk hj w).1
  by_cases h₀ : i=t
  · subst t
    obtain ⟨a,rfl⟩ := plaqEquiv.surjective i
    let i := plaquette a; let x:=a.val.1; let y:=a.val.2
    let A := sampleRow (minusRows (hessian U) (hessian V)) (coord x) (coord y)
    let B := sampleRow F i i
    let R := sampleRow (cobound 0) (coord y) vac
    let C := scaleRows (-1) (composeRows (transRows R) B)
    have hr : Whole R := sample_whole (Whole.boundary _) _ _
    have hb : Whole B := sample_whole (hu.minus hv) _ _
    have hc : Whole C := (hr.flipped.prod hb).weight _
    have hz (p : Momentum) (hp : p ∈ baseCube) : R.read p () () = q p y := by
      change (cobound 0).read _ _ _ = _; rw [Exterior.reading,sym_one]
    have hrM (p : Momentum) (hp : p ∈ baseCube) : ((transRows R).read p) () () = star (q p y) := by rw [read_opposite _ hp.1,conjTranspose_apply,hz p hp]
    have he (p : Momentum) (hp : p ∈ baseCube) : C.read p () () = -(star (q p y)*B.read p () ()) := by
      unfold C; rw [read_weight, hr.flipped.read hb hp.1,Matrix.smul_apply,Matrix.mul_apply]
      simp [hrM p hp]
    have ht : C.strip (σ/2) ((σ/2)⁻¹*X) := coax hs (A:=A) (fun _ _ => h _ _) hc x (fun p hp => by
      change (minusRows (hessian U) (hessian V)).read p (coord x) (coord y)=q p x*C.read p () ()
      rw [he p hp, read_less (hessian_whole hu).safe (hessian_whole hv).safe hp.1]; unfold U V; rw [rotor_h hk hj _ hp, rotor_h hk hj _ hp]; rw [Matrix.sub_apply]
      rw [show rotor 1 k v p (coord x) (coord y)=_ from knuckle v p a,show rotor 1 k w p (coord x) (coord y)=_ from knuckle w p a]
      change -(q p x*q (-p) y*pulse k v p i i) - _= q p x * -(star _*F.read p i i)
      unfold F
      rw [read_less hu.safe hv.safe hp.1,show U.read p=_ from (heart_see hk hj v hp).1, show V.read p=_ from (heart_see hk hj w hp).1,
         show q (-p) y = star (q p y) from (by rw [switch_axis,switch_axis,flip_chip,show star (p y)=_ from congr_fun hp.1 y]; rfl)]
      change -(q p x*star (q p y)*pulse k v p i i)- -(q p x*star (q p y)*pulse k w p i i)=_* -(_*(_-_))
      ring)
    have heq : (transRows B).strip (σ/2/2) _ := coax (A:=scaleRows (-1) (transRows C)) (by positivity : 0<σ/2) (by
      simpa only [norm_neg,norm_one,one_mul] using strip_scale (strip_trans ht) (-1)) hb.flipped y (fun p hp => by
      change (scaleRows _ _).read p () ()= q p y*(transRows B).read p () ()
      rw [read_weight, read_opposite _ hp.1, read_opposite _ hp.1]; simp [he p hp])
    convert strip_trans heq () () using 1
    change F i i=fun x=> F i i (- -x)
    simp
  let b : Cover → ℝ := F i t
  have he : b = 0 := by
    apply RRead_injective ((hu.minus hv).safe i t) (by simp)
    intro p hp; change F.read p i t = _
    unfold F; rw [read_less hu.safe hv.safe hp.1,show U.read p=_ from (heart_see hk hj v hp).1, show V.read p=_ from (heart_see hk hj w hp).1]
    simp [Matrix.sub_apply,h₀,pulse_diagonal,RRead,Laurent.read]
  change Width _ _ b; rw [he]; simp [Width,SumBudget]; positivity

lemma frost_blue (hk : 0 < k) (hj : 4 ≤ j) (v w : Train j) :
    minusRows (blue k v) (blue k w)=composeRows (composeRows (blue k v)
      (minusRows (pink k w) (pink k v))) (blue k w) := by
  obtain ⟨hb,hV⟩ := heart_h hk hj v; obtain ⟨hw,hW⟩ := heart_h hk hj w
  refine bank_injective (hV.minus hW).safe ((hV.prod (hw.minus hb)).prod hW).safe fun i=>?_
  rw [(hV.prod (hw.minus hb)).acts hW,hV.acts (hw.minus hb),hw.less hb,hV.less hW,Matrix.mul_sub,Matrix.sub_mul,
    mul_eq_one_comm.mp (heart_inverse _ hk hj v i).1,Matrix.one_mul, Matrix.mul_assoc, (heart_inverse _ hk hj w i).1, Matrix.mul_one]

structure Frost (k : ℝ) (j : ℕ) (σ η c : ℝ) : Prop where
  hue v : (pink (j:=j) k v).strip η c ∧ (blue (j:=j) k v).strip η c
  lift (X : ℝ) (v w : Train j) : 0 ≤ X → (minusRows (hessian (pink k v)) (hessian (pink k w))).strip σ X →
      (minusRows (pink k v) (pink k w)).strip η (X*c) ∧ (minusRows (blue k v) (blue k w)).strip η (X*c)

lemma possible_frost (hk : 0<k) (hj : 4 ≤ j) {σ : ℝ} (hs : 0<σ) :
    ∃ η c : ℝ, 0<η ∧ 0 ≤ c ∧ Frost k j σ η c := by
  obtain ⟨θ,K,hθ,hK,F⟩ := heart_banked k hk hj (id : Train j → _)
  let η := min θ (σ/2/2); let a := (σ/2/2)⁻¹*((σ/2)⁻¹:ℝ)
  let b := Fintype.card (TypeFace 2)*(K*(Fintype.card (TypeFace 2)*(a*K))); let c := max K (max a b)
  have hη : 0<η := lt_min hθ (by positivity); have he : K ≤ c := le_max_left ..
  have ht (i : Train j) : (pink k i).strip η K∧(blue k i).strip η K :=
    ⟨strip_mono (F i).1 (min_le_left ..) le_rfl,strip_mono (F i).2 (min_le_left ..) le_rfl⟩
  refine ⟨η,c,hη,hK.le.trans he,fun v=>⟨strip_mono (ht v).1 le_rfl he,strip_mono (ht v).2 le_rfl he⟩,?_⟩
  intro X v w hX hx
  have hg : (minusRows (pink k v) (pink k w)).strip η (X*a) := strip_mono (sight_hues hk hj hs _ _ hX hx) (min_le_right ..) (le_of_eq (by unfold a; ring))
  rw [frost_blue hk hj]
  have hu := strip_compose hη.le (strip_compose hη.le (ht v).2 (strip_flip (α:=TypeFace 2) (β:=TypeFace 2) (A:=pink k v) (B:=pink k w) hg)) (ht w).2
  refine ⟨strip_mono hg le_rfl (mul_le_mul_of_nonneg_left ((le_max_left ..).trans (le_max_right ..)) hX), strip_mono hu le_rfl ?_⟩
  exact le_trans (le_of_eq (by unfold b; ring : _=X*b)) (mul_le_mul_of_nonneg_left ((le_max_right ..).trans (le_max_right ..)) hX)
end YM.RG08.Drift
