import YM.Bid.Kitchen
import YM.Next.STATIONARY.Block.Static
import YM.Next.STATIONARY.Shape.SoftTransfers
import YM.Work.A05
import YM.Work.B18



set_option autoImplicit false
/-!
# Unit and linear phase profiles paid for. `Extension` facts local to
this L and Φ. Budgets at kicks use normed (whole view) not localized
matrix on torus.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β : Type} [Fintype α] [Fintype β] {c f L : Side} {A : Audience α} {G : Gauge} {P : Patch} {C D σ : ℝ} {m n : ℕ} {p : Momentum} {S : StepData c f}
section g
-- scalar Cast line

def arranging (P : Patch) (v z : Phase (Loc G 1)) (x y : Phase (ParcelG G P.L)) : Phase (Acts G P) := Sum.elim v (Sum.elim x (Sum.elim y z))
lemma arc_high (v z : Phase (Loc G 1)) (x y : Phase (ParcelG G P.L)) (b : Bool) : arranging P v z x y∘highVoice G P b= if b then z else v := by cases b <;> rfl
lemma arc_low (v z : Phase (Loc G 1)) (x y : Phase (ParcelG G P.L)) (b : Bool) : arranging P v z x y∘footVoice G P b= if b then y else x := by cases b <;> rfl
-- fine background template Φ test at q; Kinematics use μ epilogue.
abbrev Bridge (G : Gauge) (P : Patch) := Momentum→CompM (Co P.L (Loc G 1)) (Loc G 1)
def arriving (Φ : Bridge G P) (p : Momentum) : Phase (Loc G 1) →ₗ[ℂ] Phase (Acts G P) where
  toFun v := arranging P v 0 (Sum.elim (Φ p *ᵥ v) 0) 0
  map_add' u v := by funext x; simp only [Matrix.mulVec_add]; rcases x with x|((x|x)|(x|x)) <;> simp [arranging]
  map_smul' a b := by funext x; simp only [Matrix.mulVec_smul, RingHom.id_apply]; rcases x with x|((x|x)|(x|x)) <;> simp [arranging]

def arrives (Φ : Bridge G P) (u : Loc G 1) (p) := arriving Φ p (Pi.single u 1)
def visibly (P : Patch) (b : Bool) : Phase (ParcelG G P.L) →ₗ[ℂ] Phase (Acts G P) where
  toFun v := if b then arranging _ 0 0 0 v else arranging _ 0 0 v 0
  map_add' u v := by funext x; cases b <;> rcases x with x | (x|(x|x)) <;> simp [arranging]
  map_smul' u v := by funext x; cases b <;> rcases x with x | (x|(x|x)) <;> simp [arranging]

def velvetX (P : Patch) : Phase (Loc G 1)→ₗ[ℂ] Phase (Acts G P) where
  toFun v := arranging P 0 v 0 0
  map_add' u v := by funext x; rcases x with x | (x|(x|x)) <;> simp [arranging]
  map_smul' u v := by funext x; rcases x with x | (x|(x|x)) <;> simp [arranging]
end g
variable {Φ : Bridge G P}

lemma store_mono {x : Phase (Acts G P)} (h : Veil C x n) (p : C≤D) : Veil D x n := ⟨h.grade,fun v => (h.fine v).more (mul_le_mul_of_nonneg_left p (inch_pos _).le),fun v => (h.skins v).trans p,fun v => (h.bonds v).trans p⟩
lemma zeroPocket {f : Phase (Co L α)} (hv : f=0) (C : ℝ) (hc : 0≤C) : Hearing (balcony (Site L)) n (roster f) C := by
  apply Hearing.sup hc; intro i; rw [hv]; simpa only [show roster (0:Phase (Co L α)) i=0 from rfl, norm_zero] using hc
lemma ratePocket [DecidableEq α] {p : Momentum} {f : Phase (Co L α)} (h : p∈strip (1:ℝ)) (hv : (altarTile L α).rate p f≤1) : Hearing (balcony (Site L)) 1 (roster f) (inch L * Real.exp 4) := by
  let X := altarTile L α
  have he : slug f ≤ Real.exp 4*(inch L)⁻¹ := by
    have hp := Slab.serial_at (cruise p h) f; rw [Slab.basic_rate,one_mulVec,one_mul] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_left hv (by positivity [inch_pos L])).trans_eq (mul_one _))
  refine ⟨by positivity [inch_pos L],by omega,fun _ => ?_, by omega⟩
  have hB := pow_le_pow_left₀ (slug_nonneg _) he 2
  have hx : (balcony (Site L)).weightedSum (fun i => ‖roster f i‖^2)= (L.val:ℝ)^((-4):ℤ)*slug f^2 := by
    rw [slug_slots]; unfold Audience.weightedSum; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
    change (Fintype.card (Site L):ℝ)⁻¹ * _= _; rw [site_card]; push_cast; norm_num; rfl
  rw [hx]; apply (mul_le_mul_of_nonneg_left hB (by positivity)).trans
  unfold inch; simp; field_simp; exact le_rfl
lemma seen_affect {x : Phase (ParcelG G P.L)} (b : Bool) (h : p∈strip (1:ℝ)) (he : (slabW G P.L).rate p x≤1) : Veil (Real.exp 4) (visibly P b x) 1 := by
  classical
  let y := x ∘ Sum.inl; let z := x ∘ Sum.inr
  have hx : (altarTile P.L (Loc G 1)).rate p y≤1 := by
    have hi := Slab.serial_at (q:=p) (serial_butt (altarTile P.L (Loc G 1)) (Slab.basic (Loc G 0))) x
    rw [sliceX,one_mul] at hi; exact hi.trans he
  have hz : slug z ≤ Real.exp 4 := by
    have hi := Slab.serial_at (q:=p) (serial_brim (altarTile P.L (Loc G 1)) (Slab.basic (Loc G 0))) x
    rw [sliceY, Slab.basic_rate,one_mul] at hi; exact hi.trans (he.trans (Real.one_le_exp (by norm_num)))
  have hp : 0 ≤ inch P.L * Real.exp 4 := by positivity [inch_pos P.L]
  refine ⟨le_rfl,fun i => ?_,fun i => ?_,fun i => ?_⟩
  · cases i <;> cases b <;> first | exact zeroPocket rfl _ hp | exact ratePocket h hx
  · cases i <;> cases b <;> first | exact hz | exact (Eq.trans_le (slug_zero (α:=Loc G 0)) (Real.exp_pos 4).le)
  cases i <;> cases b <;> exact (Eq.trans_le (slug_zero (α:=Loc G 1)) (Real.exp_pos 4).le)
lemma seen_oath {u : Phase (Loc G 1)} (he : slug u ≤ 1) (hk : n ≤ 1) : Veil 1 (velvetX P u) n := by
  refine ⟨hk,fun i => ?_,fun i => ?_,fun i => ?_⟩
  · cases i <;> exact zeroPocket rfl _ (mul_nonneg (inch_pos P.L).le zero_le_one)
  · cases i <;> exact Eq.trans_le (slug_zero (α:=Loc G 0)) zero_le_one
  cases i
  · exact Eq.trans_le (slug_zero (α:=Loc G 1)) zero_le_one
  exact he
-- cast data bends. Narrow API on Φ unit-amplitude.
def Ties (Φ : Bridge G P) (σ C : ℝ) := ∀ p∈ strip σ, ∀ v : Loc G 1, ∀ i, ‖roster (Φ p *ᵥ Pi.single v 1) i‖ ≤ inch P.L*C
lemma bends_affect (hz : 1 ≤ C) (h : Ties Φ σ C) (hp : p∈strip σ) (i : Loc G 1) : Veil C (arrives Φ i p) 0 := by
  have he := h p hp i
  have ht : 0≤ C := zero_le_one.trans hz
  have hv := mul_nonneg (inch_pos P.L).le ht
  refine ⟨by decide,fun a => ?_,fun a => ?_,fun a => ?_⟩
  · cases a
    · exact Hearing.sup hv he
    exact zeroPocket rfl _ hv
  · cases a <;> exact Eq.trans_le (slug_zero (α:=Loc G 0)) ht
  cases a
  · exact Eq.trans_le (slug_unit i) hz
  exact Eq.trans_le (slug_zero (α:=Loc G 1)) ht
end YM.Stationary
end

/-!
# Shim lenses for scalar vertices. No ℓ¹ over rough aliases. Location
uses cell flux and orientation picked by lift; imaginary kicks allowed up to
σ/L at S terms. `flot` charges ACTUAL kernel locations. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α ι G' : Type} [Fintype α] [DecidableEq α] {G : Gauge} {t n : ℕ} {c f m L : Side} {p : Momentum} {σ C : ℝ}

section flot
variable (l : Stitch t) (k : Tailor t→ℂ) (b : Breed t α) (p : Breed t Momentum)

def flotilla (x : Tailor t) (v : Breed t (Phase (Co L α))) :=
    ∑ z : Site L,(∏ i, scrap (p i) (flight (p i) (l i) (v i)) (lift z+legLane x i) (b i))*k x

def flot (v : Breed t (Phase (Co L α))) := ∑' x, flotilla l k b p x v

lemma flot_signal (he : Width σ C k) (hw : 0≤σ) (g : Ratio c f) {q : Breed t (Site c)} (h : ∀ i, rolls (mon (q i)) (p i)) (v : Breed t (Phase (Co g.count α))) :
    pinRing l k b f (fun i => poured g (q i) (v i))= if ∑ i,q i=0 then (Fintype.card (Site c):ℂ)*flot l k b p v else 0 := by
  rw [pinRing_on _ _ _ he hw]
  let M (z : Tailor t) := ∑ x : Site f,pinion l k b z x (fun i => poured g (q i) (v i))
  have ht z : M z=(∑ x, cell (∑ i,q i) x)*flotilla l k b p z v := by
    unfold M flotilla
    rw [← Equiv.sum_comp (Equiv.ofBijective g.assemble g.assemble_bijective), sum_mul,Fintype.sum_prod_type]; apply sum_congr rfl; intro x _; rw [mul_sum]; apply sum_congr rfl; intro y _
    rw [pinion_eval]; change (∏ i,swingD (l i) _ (g.assemble (x,y)+wrap f (legLane z i),b i))*_=_
    have he (i) : g.assemble (x,y)+wrap f (legLane z i)=wrap f (lift y+legLane z i)+g.embed x := by rw [map_add]; unfold Ratio.assemble; abel
    simp_rw [he,flight_price g _ (h _),Finset.prod_mul_distrib]; rw [cell_prod_hymn,mul_assoc]
  change ∑' z,M z=_
  simp_rw [ht,tsum_mul_left]; split
  next hz => rw [hz]; simp [cell]; rfl
  next hz => rw [sum_cell hz,zero_mul]

lemma flot_tides {r : Breed t Momentum} (h : ∀ i, rolls (p i) (r i)) (v : Breed t (Phase (Co L α))) : flot l k b p v=flot l k b r v := by
  unfold flot flotilla; simp_rw [scrap_reset (h _), flight_reset (h _)]
end flot
section costs
variable {p : Momentum} {R : ℝ}

lemma rot_seat {f : Site L → ℂ} (a : Site L) (he : Hearing (balcony _) n f C) : Hearing (balcony _) n (fun i => f (i+a)) C :=
    ⟨he.cap,fun p i=> he.all p _,fun p => ((Equiv.sum_comp (Equiv.addRight a) _).trans_le (he.ample p)), fun p => ((Equiv.sum_comp (Equiv.addRight a) _).trans_le (he.enough p))⟩
lemma invoice (u : Phase (Co L α)) (x : Cover) (i : α) (he : Hearing (balcony _) n (fun j : Site L => u (j,i)) R)
    (hs : 0<σ) (h : p∈strip σ) : Hearing (balcony _) n (fun a : Site L => scrap p u (lift a+x) i) (Real.exp (σ*(8+inch L*Laurent.size x))* R) := by
  have hv := rot_seat (wrap L x) he
  apply hv.grows _ (by positivity); intro a; rw [scrap,norm_mul,map_add,wrap_lift]
  refine mul_le_mul_of_nonneg_right ((reward _ _ σ (fun i => (h i).le)).trans ?_) (norm_nonneg _)
  apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ hs.le
  apply (rent_cost ..).trans
  have ht : (Laurent.size (lift a+x):ℝ) ≤ Laurent.size (lift a)+(Laurent.size x:ℝ) := by exact_mod_cast Laurent.size_add (lift a) x
  have hi := inch_pos L; nlinarith only [plank_charge L a, ht,hi]
-- ℓ^k weights used for mixed internal derivatives. t external, T shell.
lemma Hearing.stockpile [Fintype ι] {A : Audience ι} (s : Finset G') (f : G'→ι→ℂ) {C : G'→ℝ} {x : G'→ℕ}
    (h : ∀ i∈s,Hearing A (x i) (f i) (C i)) : Hearing A (∑ i∈s,x i) (fun v => ∏ i∈s,f i v) (∏ i∈s,C i) := by
  classical induction s using Finset.induction with
  | empty => simpa using Hearing.sup (A:=A) (f:=fun _=>(1:ℂ)) (n:=0) (C:=1) zero_le_one (by simp)
  | insert i s he ih => simp_rw [sum_insert he,prod_insert he]; exact Hearing.multiplied (f:=f i) (fun j => (norm_mul ..).le) (h i (by simp)) (ih fun j hj => h _ (by simp [hj]))

lemma yarn (x : Tailor t) : ∑ i, Laurent.size (legLane x i)=Laurent.size x := by
  unfold Laurent.size legLane
  rw [Fin.sum_univ_succ,Fintype.sum_prod_type]; simp only [Fin.cons_zero,Fin.cons_succ,Pi.zero_apply, Int.natAbs_zero,sum_const_zero,zero_add]

variable (l : Stitch t) (k : Tailor t→ℂ) (b : Breed t α) (p : Breed t Momentum)

def robinTax (σ : ℝ) (t : ℕ) := Real.exp (σ*((t+1)*8))
lemma flot_cash (hs : 0<σ) (hw : ∀ i,p i∈strip σ) (v : Breed t (Phase (Co L α))) (R : Breed t ℝ) {n : Breed t ℕ}
    (hp : ∀ i,Hearing (balcony _) (n i) (fun j : Site L => flight (p i) (l i) (v i) (j,b i)) (R i)) (hv : ∑ i,n i ≤2)
    (z : Tailor t) : ‖flotilla l k b p z v‖≤((L.val:ℝ)^4*((∏ i,R i)*robinTax σ t))*(Real.exp (inch L*σ*Laurent.size z)*‖k z‖) := by
  let U (i : Fin (t+1)) (j : Site L) := scrap (p i) (flight (p i) (l i) (v i)) (lift j + legLane z i) (b i)
  have hy i : Hearing (balcony (Site L)) (n i) (U i) _ := invoice (flight (p i) (l i) (v i)) (legLane z i) (b i) (hp i) hs (hw i)
  have ht := (Hearing.stockpile univ U (fun i _ => hy i)).rasp hv
  have hx : ∑ j : Site L, ‖∏ i,U i j‖ ≤ (L.val:ℝ)^4*((∏ i,R i)*robinTax σ t)*Real.exp (inch L*σ*Laurent.size z) := by
    unfold Audience.weightedSum balcony at ht
    simp_rw [site_card, Nat.cast_pow,inv_mul_eq_div] at ht
    rw [← sum_div] at ht
    replace ht := (div_le_iff₀ (by positivity)).1 ht
    refine ht.trans_eq ?_
    symm; unfold robinTax
    rw [prod_mul_distrib, ← Real.exp_sum,_root_.mul_assoc ((L.val:ℝ)^4), _root_.mul_assoc, ← Real.exp_add, ← mul_sum]
    have he : (∑ i,(8+inch L* Laurent.size (legLane z i):ℝ))=((t+1:ℝ)*8+inch L*Laurent.size z) := by
      rw [sum_add_distrib,← mul_sum, ← Nat.cast_sum, yarn]; simp
    rw [he]; ring_nf
  unfold flotilla; rw [← Finset.sum_mul,norm_mul]; exact (mul_le_mul_of_nonneg_right ((norm_sum_le ..).trans hx) (norm_nonneg _)).trans_eq (by ring)
end costs
end YM.Stationary
end

/-! # Flight circulation. -/
noncomputable section
namespace YM.Stationary
open Function Filter Metric Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α ι G' : Type} [Fintype α] [DecidableEq α] {G : Gauge} {t n : ℕ} {c f m L : Side} {p : Momentum} {σ C : ℝ}

section rec
variable (l : Stitch t) (k : Tailor t→ℂ) (b : Breed t α)
variable (p : Breed t Momentum)

def soaring (z : Tailor t) : RecordM ℂ (Fin (t+1)) (Co L α) := ∑ i : Site L, (MultilinearMap.mkPiRing ℂ (Fin (t+1)) (k z)).compLinearMap (fun j => LinearMap.proj (i,b j) ∘ₗ twitches (p j) (legLane z j) ∘ₗ flight (p j) (l j))
def steerRec : RecordM ℂ (Fin (t+1)) (Co L α) := flyRec (soaring l k b p)
lemma soaring_eval (v : Breed t (Phase (Co L α))) (z) : soaring l k b p z v=flotilla l k b p z v := by
  rw [soaring,_root_.sum_apply]; rfl
lemma flot_worth (hc : Width (inch L*σ) C k) (hs : 0<σ) (hw : ∀ i,p i∈strip σ)
    (u : Breed t (Phase (Co L α))) (R : Breed t ℝ) {n : Breed t ℕ}
    (hp : ∀ i,Hearing (balcony _) (n i) (fun j : Site L => flight (p i) (l i) (u i) (j,b i)) (R i)) (hv : ∑ i,n i ≤2) :
    ‖flot l k b p u‖ ≤ ((L.val:ℝ)^4*((∏ i,R i)*robinTax σ t))*C := by
  let V : ℝ := (L.val:ℝ)^4*((∏ i,R i)*robinTax σ t)
  have he : 0 ≤ V := by unfold V robinTax; apply mul_nonneg (by positivity); exact mul_nonneg (prod_nonneg fun i _ => (hp i).cap) (by positivity)
  have hh x := flot_cash l k b p hs hw u R hp hv x
  have H := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hh (hc.2.1.mul_left V)
  refine (norm_tsum_le_tsum_norm H).trans ((H.tsum_le_tsum hh (hc.2.1.mul_left V)).trans ?_)
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hc.2.2 he
lemma steerRec_rec (h : Width (inch L*σ) C k) (hs : 0<σ) (hw : ∀ i,p i∈strip σ) (u : Breed t (Phase (Co L α))) : steerRec (L:=L) l k b p u=flot l k b p u := by
  have hV (v : Breed t (Phase (Co L α))) : Summable (fun i=>soaring l k b p i v) := by
    let R (j : Fin (t+1)) := ‖flight (p j) (l j) (v j)‖
    have hh j : Hearing (balcony _) 0 (fun i : Site L => flight (p j) (l j) (v j) (i,b j)) (R j) := Hearing.sup (norm_nonneg _) (fun i => norm_le_pi_norm _ _)
    simp_rw [soaring_eval]; exact Summable.of_norm_bounded (h.2.1.mul_left _) (flot_cash _ _ _ _ hs hw _ R hh (by simp))
  rw [steerRec,flyRec_recites _ hV]; simp_rw [soaring_eval]; rfl
end rec
section bill
variable (l : Stitch t) (k : Tailor t→ℂ) (b : Breed t α)
private lemma flairs (s : List Axis) : Differentiable ℂ (fun x : Momentum × Phase (Co L α) => flight x.1 s x.2) := by
  apply differentiable_pi.mpr; intro i
  induction s generalizing i with
  | nil => change Differentiable ℂ (fun x : Momentum × Phase (Co L α) => x.2 i); fun_prop
  | cons j s ih =>
    let F := fun x : Momentum × Phase (Co L α) => flight x.1 s x.2
    change Differentiable ℂ (fun x => scrap _ (F x) (lift i.1+step j) i.2 - F x i)
    unfold scrap; apply (Differentiable.mul ?_ (ih _)).sub (ih i); unfold mode; fun_prop
private lemma flairs_pin (v : Fin (t+1)) : Differentiable ℂ (fun x : (Breed t Momentum) × (Breed t (Phase (Co L α))) => flight (x.1 v) (l v) (x.2 v)) := (flairs (α:=α) (L:=L) (l v)).comp (show Differentiable ℂ (fun x : Breed t Momentum × Breed t (Phase (Co L α)) => (x.1 v,x.2 v)) by fun_prop)

private lemma localDifP {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {G : Type} {s : Finset G} {f : G → X→ℂ}
    (h : ∀ i∈s,Differentiable ℂ (f i)) : Differentiable ℂ (fun x=>∏ i∈s,f i x) := by
  classical induction s using Finset.induction with
  | empty => simp [differentiable_const]
  | insert i s he ih => simp_rw [prod_insert he]; exact Differentiable.mul (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

private lemma billboard (z) : Differentiable ℂ (fun x : (Breed t Momentum) × (Breed t (Phase (Co L α))) => flotilla l k b x.1 z x.2) := by
  unfold flotilla; apply Differentiable.fun_sum; intro i _; apply Differentiable.mul_const; apply localDifP; intro j _
  unfold scrap; apply (show Differentiable ℂ (fun x : (Breed t Momentum) × Breed t (Phase (Co L α)) => mode (x.1 j) (rent L (lift i+legLane z j))) by unfold mode; fun_prop).mul; exact differentiable_pi.mp (flairs_pin l j) _
set_option maxHeartbeats 430000 in
lemma flot_bill (hs : 0<σ) (hw : Width (inch L*σ) C k) (x : (Breed t Momentum) × (Breed t (Phase (Co L α)))) (hv : ∀ i,x.1 i ∈ strip σ) :
    DifferentiableAt ℂ (fun p : (Breed t Momentum) × (Breed t (Phase (Co L α))) => flot l k b p.1 p.2) x := by
  let V (y : (Breed t Momentum) × (Breed t (Phase (Co L α)))) i := ‖flight (y.1 i) (l i) (y.2 i)‖
  let R (i) := V x i +1
  have hh : ∀ᶠ y in 𝓝 x,∀ i, V y i<R i ∧ y.1 i∈strip σ := by
    apply eventually_all.mpr; intro i
    have hg : ContinuousAt (fun y => V y i) x := (flairs_pin (α:=α) (L:=L) l i).continuous.norm.continuousAt
    exact (hg.tendsto.eventually (gt_mem_nhds (show V x i<R i by unfold R; linarith))).and
      ((show Continuous (fun y : (Breed t Momentum) × (Breed t (Phase (Co L α)))=> y.1 i) by fun_prop).continuousAt.tendsto.eventually ((Work.F07.stripOpen σ).mem_nhds (hv i)))
  obtain ⟨r,hr,H⟩ := Metric.mem_nhds_iff.mp (show {y | ∀ i,V y i<R i ∧ y.1 i∈strip σ}∈𝓝 x from hh)
  refine (Work.F02.analytic_series (x:=x) (fun i (p : Breed t Momentum × Breed t (Phase (Co L α))) => flotilla l k b p.1 i p.2) hr (fun i=> billboard l k b i) (hw.2.1.mul_left ((L.val:ℝ)^4*((∏ j,R j)*robinTax σ t))) ?_).differentiableAt
  intro i y hy
  have he : ∀ j,V y j<R j ∧ y.1 j∈strip σ := H hy
  have hb j : Hearing (balcony _) 0 (fun i : Site L => flight (y.1 j) (l j) (y.2 j) (i,b j)) (R j) := Hearing.sup ((show 0≤ V y j from norm_nonneg _).trans (he j).1.le) fun i => (norm_le_pi_norm _ _).trans (he j).1.le
  exact flot_cash l k b y.1 hs (fun j => (he j).2) y.2 R hb (by simp) i
end bill
end YM.Stationary
end

/-! # Stitch receipts to the mesh. Derivative rank on scalar after evaluating f. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α ι G' : Type} [Fintype α] [DecidableEq α] [Fintype ι] {G : Gauge} {t n : ℕ} {c f m L : Side} {p : Momentum} {σ C A : ℝ}

section feature
abbrev Needle (ι α : Type) (t : ℕ) := Breed t α → ι → Tailor t → ℂ
variable (l : ι → Stitch t) (F : Needle ι α t)

def tunnels (p : Breed t Momentum) : RecordM ℂ (Fin (t+1)) (Co L α) := ∑ j : Breed t α, ∑ i:ι, steerRec (l i) (F j i) j p

def Dai (σ C : ℝ) := ∀ i j,Width σ C (F i j)

lemma tunnels_green (h : Dai F (inch L*σ) C) (hw : 0<σ) {p : Breed t Momentum} (hv : ∀ i,p i∈strip σ) (v : Breed t (Phase (Co L α))) :
    tunnels l F p v=∑ j : Breed t α, ∑ i : ι, flot (l i) (F j i) j p v := by
  unfold tunnels; simp_rw [_root_.sum_apply, steerRec_rec _ _ _ _ (h _ _) hw hv]
lemma tunnels_bill (h : Dai F (inch L*σ) C) (hs : 0<σ) (x : (Breed t Momentum) × (Breed t (Phase (Co L α)))) (hx : ∀ i, x.1 i∈strip σ) :
    DifferentiableAt ℂ (fun x : (Breed t Momentum) × (Breed t (Phase (Co L α))) => tunnels l F x.1 x.2) x := by
  have he : ∀ᶠ y in 𝓝 x,∀ i,y.1 i∈strip σ := eventually_all.mpr fun i =>
    (show Continuous (fun y : (Breed t Momentum) × (Breed t (Phase (Co L α))) => y.1 i) by fun_prop).continuousAt.tendsto.eventually ((Work.F07.stripOpen σ).mem_nhds (hx i))
  refine DifferentiableAt.congr_of_eventuallyEq (DifferentiableAt.fun_sum (u:=univ) (fun i _ => DifferentiableAt.fun_sum (u:=univ) (fun j _=> flot_bill (l j) _ i hs (h i j) x hx))) ?_
  filter_upwards [he] with y hy; exact tunnels_green _ _ h hs hy _
lemma tunnels_twist {p r : Breed t Momentum} (h : ∀ i,rolls (p i) (r i)) : tunnels l F p=(tunnels l F r : RecordM ℂ (Fin (t+1)) (Co L α)) := by
  unfold tunnels steerRec
  refine sum_congr rfl fun b _ => sum_congr rfl fun j _ => ?_
  apply congr_arg (flyRec (α:=Co L α)); funext z
  apply MultilinearMap.ext; intro v
  rw [soaring_eval,soaring_eval]; unfold flotilla; simp_rw [scrap_reset (h _),flight_reset (h _)]
lemma tunnels_book (h : Dai F (inch L*σ) C) (hs : 0<σ) {p : Breed t Momentum} (hw : ∀ i,p i∈strip σ) (u : Breed t (Phase (Co L α))) (R : ι→Breed t ℝ) {n : Breed t ℕ}
    (hp : ∀ a i j,Hearing (balcony _) (n i) (fun z : Site L => flight (p i) (l a i) (u i) (z,j)) (R a i))
    (hv : ∑ i,n i ≤2) (hg : 0≤ C) (hr : ∀ a, (L.val:ℝ)^4*(∏ i,R a i) ≤ A) :
    ‖tunnels l F p u‖ ≤ ((Fintype.card (Breed t α):ℝ)*Fintype.card ι*robinTax σ t)*A*C := by
  rw [tunnels_green l F h hs hw]; refine (norm_sum_le ..).trans ?_
  rw [show ((Fintype.card (Breed t α):ℝ)*Fintype.card ι*robinTax σ t)*A*C= ∑ _ : Breed t α, ∑ _ : ι,A*robinTax σ t*C by simp; ring]
  refine sum_le_sum fun j _ => (norm_sum_le ..).trans (sum_le_sum fun i _ => ?_)
  refine (flot_worth (l i) (F j i) j _ (h j i) hs hw _ _ (fun k=>hp i k (j k)) hv).trans ?_; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hr i) (Real.exp_pos _).le) hg
end feature
section fine
variable {F : Needle ι (Loc G 1) t} {l : ι → Stitch t}

def Cargo (l : ι → Stitch t) (F : Needle ι (Loc G 1) t) (f : Link G m →ℝ) := noteAt f (t+1)=∑ j,∑ i,pinRing (l i) (F j i) j m

def Spool (Q : Picture G t) (l : ι → Stitch t) (F : Needle ι (Loc G 1) t) := ∀ a b p,star p=p → Q a b p=∑ i,factorRay (l i) (F (fun i => (b i,a i)) i) p

lemma spooling {Q : Picture G t} {f : Link G m→ℝ} (hs : 0<σ) (hp : Spool Q l F) (h : Dai F σ C) (he : Recorded Q f 0) : Cargo l F f := by
  apply relay_ext; intro p; let i := fun j=> (p j).2.2; let b := fun j=> (p j).2.1; let x := Prod.fst ∘ p
  rw [show (fun j => relay (p j).1 (p j).2)=glyph x i b from rfl, (record_exact ..).1 he x i b]; unfold glyph collected
  let a (k : Fin (t+1)) := (b k,i k)
  simp_rw [_root_.sum_apply,pinRing_rec _ _ _ (h _ _) hs.le]; split
  next hz => rw [hp _ _ _ (out_real x), mul_sum, Finset.sum_eq_single a]
             · simp [a,hz]
             · intro v hv hy; simp_rw [if_neg (show ¬ (v = (fun i' => (b i',i i')) ∧ ∑ j,x j=0) from fun hc => hy hc.1)]; simp
             simp
  next hz => simp [hz]

-- per-cell, full (all internal aliases)
lemma cargo_tick (g : Ratio c f) {U : Link G f→ℝ} (h : Dai F (inch g.count *σ) C) (he : Cargo l F U) {q : Breed t (Site c)} {p : Breed t Momentum} (hr : ∀ i, rolls (mon (q i)) (p i)) (hs : 0<σ) (v : Breed t (Phase (Co g.count (Loc G 1)))) :
    noteAt U (t+1) (fun i => poured g (q i) (v i)) = if ∑ i,q i=0 then (Fintype.card (Site c):ℂ)*tunnels l F p v else 0 := by
  have hx i : star (p i)=p i := by obtain ⟨a,ha⟩ := hr i; rw [ha,star_add,real_frequency]; congr 1; ext1 j; simp [reciprocal]
  have hp : ∀ i,p i∈strip σ := fun i => Work.F07.realStrip _ hs (hx _)
  have hz : 0 < inch g.count *σ := mul_pos (inch_pos _) hs
  unfold Cargo at he; rw [he,tunnels_green _ _ h hs hp]; simp_rw [_root_.sum_apply, flot_signal _ _ _ _ (h _ _) hz.le g hr]; split <;> next hh=> simp [hh, Finset.mul_sum]
end fine
end YM.Stationary
end

/-!
# Choice over sting placements preserving number of difference payments
on independent slots. B for tags may be empty too. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α ι : Type} [Fintype α] [DecidableEq α] {G : Gauge} {t n : ℕ} {c f m L : Side} {p : Momentum} {σ C A : ℝ}

abbrev Ports (t n : ℕ) := Fin n→Keys t

def tabsZ {α : Type} [DecidableEq α] (a : List (α × Axis)) (i : α) := (a.filter (fun j => j.1=i)).map (Prod.snd)

def roller (r : Fin n→Fin (t+1)) (x : Ports t n) : Stitch t := tabsZ ((List.finRange n).map (fun i => (r i,(x i).2)))
def winglet (t n : ℕ) (x : Ports t n) := roller (fun i => (x i).1.succ) x

theorem tabsZ_pay (P : α→Momentum) (a : List (α × Axis)) : ∏ i : α,sparksZ (P i) (tabsZ a i)=(a.map fun j=> Exterior.q (P j.1) j.2).prod := by
  induction a with
  | nil => simp [tabsZ,sparksZ]
  | cons j a ih =>
    conv_rhs => rw [List.map_cons,List.prod_cons,← ih]
    rw [show Exterior.q (P j.1) j.2=(∏ v : α,(if j.1=v then Exterior.q (P j.1) j.2 else 1)) by simp,← prod_mul_distrib]; apply prod_congr rfl; intro i _
    by_cases he : j.1=i <;> simp [tabsZ,he]

theorem wing_factor (r : Fin n→Fin (t+1)) (x : Ports t n) (P : Breed t Momentum) : ∏ j,sparksZ (P j) (roller r x j)=∏ j,Exterior.q (P (r j)) (x j).2 := by
  rw [roller,tabsZ_pay,Fin.prod_univ_def]; rw [List.map_map]; rfl
private lemma tabsZ_size (a : List (α × Axis)) : ∑ i : α, (tabsZ a i).length=a.length := by
  induction a with
  | nil => simp [tabsZ]
  | cons j s ih =>
    calc
      _ = ∑ i : α, ((tabsZ s i).length+ if j.1=i then 1 else 0) := sum_congr rfl fun i _ => by by_cases h : j.1=i <;> simp [tabsZ,h]
      _ = _ := by simp [sum_add_distrib,ih]
lemma roller_extent (r : Fin n→Fin (t+1)) (x : Ports t n) : ∑ j,(roller r x j).length=n := by rw [roller,tabsZ_size]; simp
lemma winglet_port (x : Ports t n) : winglet t n x 0=[] := by
  unfold winglet roller tabsZ; simp
lemma roller_ge {t n : ℕ} (r : Fin n → Fin (t+1)) (x : Ports t n) (i) : (roller r x i).length ≤ n :=
    (single_le_sum (s:=univ) (f:=fun i => _) (fun i _ => Nat.zero_le (roller r x i).length) (mem_univ i)).trans_eq (roller_extent r x)

lemma winding (t n : ℕ) (hs : 0<σ) : ∃ η C,0<η ∧ 0≤C ∧ ∀ (A : ℝ),0≤A → ∀ (F : Picture G t),
    (∀ i j, Firm σ A (F i j) ∧ Rays n (F i j ∘ axes)) → ∃ k : Needle (Ports t n) (Loc G 1) t, Dai k η (A*C) ∧ Spool F (winglet t n) k := by
  obtain ⟨η,K,hτ,_,hK,h⟩ := transfers n t hs
  refine ⟨η,K,hτ,hK,fun A hA F hF => ?_⟩
  choose k he ht using fun i j => h A hA _ (hF i j).1 (hF i j).2
  refine ⟨fun i => k (Prod.snd ∘ i) (Prod.fst ∘ i),fun i j => he _ _ _,fun i j p hP => ?_⟩
  rw [ht i j p (Work.F07.realStrip _ hτ hP)]
  apply sum_congr rfl; intro b _; unfold factorRay; rw [winglet,wing_factor]; rfl

lemma windTwin (n : ℕ) (r : Fin n→Fin 2) (hs : 0<σ) : ∃ η K,0<η ∧ 0≤K ∧ ∀ (A : ℝ), 0 ≤ A → ∀ F : Picture G 1,
    (∀ i j, Firm σ A (F i j) ∧ Rays n (F i j ∘ axes)) → ∃ k : Needle (Ports 1 n) (Loc G 1) 1, Dai k η (A*K) ∧ Spool F (roller r) k := by
  obtain ⟨η,K,hτ,_,hK,h⟩ := twin_layers n r hs
  refine ⟨η,K,hτ,hK,fun A hA F hF => ?_⟩
  choose k he ht using fun i j => h A hA _ (hF i j).1 (hF i j).2
  refine ⟨fun i => k (Prod.snd ∘ i) (Prod.fst ∘ i),fun i j => he _ _ _,fun i j p hP => ?_⟩
  rw [ht i j p (Work.F07.realStrip _ hτ hP)]
  apply sum_congr rfl; intro b _; unfold factorRay; rw [wing_factor]; rfl
end YM.Stationary
end
