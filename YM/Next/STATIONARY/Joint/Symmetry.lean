import YM.Next.STATIONARY.Joint.HaarJac
import YM.Next.STATIONARY.Shape.ClassicalMatch


set_option autoImplicit false
/-!
# Both covariance groups transported in ROOTED coordinates.

Bound `legion` is off-shell too. `bounty`/full determinant compared here
using actual damage on (possibly moved) Shell or anywhere its classical
action in corresponding charts is analytic. In signed symmetry operations `burn` may be read at inverted links
(the fine auxiliary vectored determinant will not claim ALL signed symmetries).
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma gram_bend {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (T : Funds κ) {U : Funds ι}
    (A B : Matrix κ ι ℝ) (h : Military T) (he : B*U=T*A) : Uᵀ*(Bᵀ*B)*U=Aᵀ*A := by
  rw [← Matrix.mul_assoc Uᵀ Bᵀ,Matrix.mul_assoc (_*_ : Matrix ι κ ℝ) B,← transpose_mul,he, transpose_mul,Matrix.mul_assoc,← Matrix.mul_assoc Tᵀ,h.right,Matrix.one_mul]

lemma frame_log_shift (k : Coats G n) : ∀ᶠ u : Coats G n in 𝓝 1, frameLog (k*u*k⁻¹)=armorG k (frameLog u) := by
  have he i := ((continuous_apply i).tendsto (1:Coats G n)).eventually (plog_conj (k i))
  filter_upwards [eventually_all.mpr he] with U hu
  apply gaugeColor.injective; funext i
  rw [armorG_at,frameLog,frameLog, gaugeColor.apply_symm_apply,gaugeColor.apply_symm_apply]; exact hu i
lemma link_log_k (k : Coats G n) : ∀ᶠ U in 𝓝 (1:Config G n), content (fun e => k e.1*U e*(k e.1)⁻¹)=armor k (content U) := by
  have he (e : Edge (Site n)) := ((continuous_apply e).tendsto (1:Config G n)).eventually (plog_conj (k e.1))
  filter_upwards [eventually_all.mpr he] with U hu
  apply edgeColor.injective; funext e
  rw [armor_at]
  change arm _ _ _ _ _ = G.adjoint _ (arm _ _ _ _ _); rw [content_at,content_at]; exact hu e
lemma rear_tactics (k : Coats G f) (u : Coats G c) : rearM G c f*tactics k u=trench k * rearM G c f := by
  apply bill_eq (helmets G c f); intro x; rw [← Matrix.mulVec_mulVec,tactics,bill_at,rear_cost,← Matrix.mulVec_mulVec,rear_cost,trench,bill_pay]; rfl

lemma rate_transfer {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (P : Basis ι ℝ X) (Q : Basis κ ℝ Y) (A : X →L[ℝ] X) (B : Y →L[ℝ] Y) {F H : X→Y} (h : F ∘ A =ᶠ[𝓝 0] B ∘ H)
    (hv : ContDiffAt ℝ ω F 0) (he : ContDiffAt ℝ ω H 0) :
    billsM P Q (fderiv ℝ F 0)*billsM P P A=billsM Q Q B*billsM P Q (fderiv ℝ H 0) := by
  have hp := h.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp _ (by rw [map_zero]; exact hv.differentiableAt (by simp)) A.differentiableAt, map_zero,A.fderiv, fderiv_comp _ B.differentiableAt (he.differentiableAt (by simp)),B.fderiv] at hp
  rw [← bill_multiply,← bill_multiply,hp]

private lemma choir {ι κ : Type} [Fintype ι] [Fintype κ] {A B : Matrix κ ι ℝ} {U : Funds ι} {T P Q : Funds κ}
    (h : A*U=T*B) (hp : Tᵀ*P*T=Q) : Uᵀ*(Aᵀ*P*A)*U=Bᵀ*Q*B := by
  rw [show Uᵀ * (Aᵀ*P*A)*U=(A*U)ᵀ*P*(A*U) by rw [transpose_mul]; simp only [Matrix.mul_assoc], h,transpose_mul,← hp]; simp only [Matrix.mul_assoc]

-- V fixed but transformed according to coarse gauge; actual matrices
section congress
variable (h : S.patch.Branches S.kernel G) (t : S.Choices) (k : Coats G f) (u : Coats G c)
    (U : Joint G c f) (V : Config G c)
    {p : Clip} {R : PathData G} {μ σ A Λ : ℝ}
include h

lemma horn (hv : Explosives S t 1 U) :
    rocket S t 1 (wages S k u U) ∘ armUp k u =ᶠ[𝓝 0] armorG k ∘ rocket S t 1 U := by
  let L := fun x => (shield S t (dress 1 U))⁻¹ * shield S t (atire 1 U x)
  have he : L 0=1 := by simp [L]
  have hp : Army L 0 := (Army.park _ _).mul hv.pins
  filter_upwards [(show Tendsto L _ (𝓝 1) from he ▸ hp.cont.tendsto).eventually (frame_log_shift k)] with x hx
  rw [Function.comp_apply,Function.comp_apply,rocket,rocket,map_neg]
  congr 1
  change _=armorG k (frameLog (L x)); rw [← hx]
  simp only [atire,dress_one,arm_root,shields S t h,L]; congr 1
  funext i; simp; group
lemma quota_k (hv : Teller S t p R 1 U) :
    worn S t 1 (wages S k u U) ∘ armUp k u =ᶠ[𝓝 0] armor u ∘ worn S t 1 U := by
  let F x := ribbon S t (atire 1 U x) * (ribbon S t (dress 1 U))⁻¹
  have he : F 0=1 := by simp [F]
  have hp : Army F 0 := hv.thorn.mul (Army.park _ _)
  filter_upwards [(show Tendsto F _ (𝓝 1) from he ▸ hp.cont.tendsto).eventually (link_log_k u)] with x hx
  rw [Function.comp_apply, Function.comp_apply,worn,worn]
  change _=armor u (content (F x)); rw [← hx]
  simp only [atire,dress_one,arm_root,ribbons S t h,F]; congr 1
  funext i; simp [Lattice.gauge]; group

lemma munition_law (hp : Explosives S t 1 U) (hw : Explosives S t 1 (wages S k u U)) (ht : 0<μ) :
    cannonade S t μ 1 (wages S k u U)*tactics k u=troop k * cannonade S t μ 1 U := by
  have he := rate_transfer (helmets _ _ _) (pocket _) _ _ (horn h t k u U hp) (market S t 1 _ hw) (market S t 1 _ hp)
  rw [cannonade,cannonade,Matrix.add_mul, Matrix.mul_add,Matrix.mul_assoc,rear_tactics,← Matrix.mul_assoc]
  rw [show (wages S k u U).1=Lattice.gauge k U.1 from rfl, (troop_orthogonal k).transpose_cross (trench_orthogonal k) (mail_carry k U.1),Matrix.mul_assoc]
  rw [Matrix.mul_assoc,show indexX _ _ _ _*tactics k u=troop k * indexX S t 1 U from he, ← Matrix.mul_assoc (cannon μ _), (battery _ ht k).1, Matrix.mul_assoc]
lemma gear_honors (hp : Explosives S t 1 U) (hw : Explosives S t 1 (wages S k u U)) (ht : 0<μ) :
    (tactics k u)ᵀ*militia S t μ 1 (wages S k u U)*tactics k u=militia S t μ 1 U := gram_bend _ _ _ (troop_orthogonal _) (munition_law h t k u U hp hw ht)
lemma honors_status (he : R.Bounds p σ A Λ) (hp : Explosives S t 1 U) (hw : Explosives S t 1 (wages S k u U)) (ht : 0<μ)
    (hb : ContDiffAt ℝ ω (canon S t p R (Lattice.gauge u V) (wages S k u U)) 0) :
    (tactics k u)ᵀ*medals S t p R μ 1 (Lattice.gauge u V) (wages S k u U)*tactics k u=medals S t p R μ 1 V U := by
  rw [medals,medals,cannon_law,cannon_law,Matrix.mul_add,Matrix.add_mul,gear_honors h t k u U hp hw ht]
  congr 1; exact (damage_rate _ (helmets _ _ _) _ _ hb).symm.trans (by rw [canon_carry S t p R h he])
lemma bounty_carry (he : R.Bounds p σ A Λ) (hp : Explosives S t 1 U) (hw : Explosives S t 1 (wages S k u U)) (ht : 0<μ)
    (hb : ContDiffAt ℝ ω (canon S t p R (Lattice.gauge u V) (wages S k u U)) 0) :
    bounty S p R μ t 1 (Lattice.gauge u V) (wages S k u U)= bounty S p R μ t 1 V U := by
  simp only [bounty,(tactics_orthogonal _ _).turn_det (honors_status h t k u U V he hp hw ht hb),show (wages S k u U).1=Lattice.gauge k U.1 from rfl, (troop_orthogonal k).turn_det ((troop_orthogonal k).back (battery _ ht k |>.2))]

end congress
section comparison
variable (k : Coats G n) {p : Clip} {R : PathData G} {σ A Λ : ℝ} (hp : R.Bounds p σ A Λ)
include hp
lemma burn_carry (U : Config G n) : burn p R (Lattice.gauge k U) ∘ (armor k)= burn p R U := funext fun i => by rw [Function.comp_apply,burn,armor_go, Work.F05.mainTerm_gauge hp]; rfl
lemma flare_carry (U : Config G n) (he : ContDiffAt ℝ ω (burn p R (Lattice.gauge k U)) 0) :
    (trench k)ᵀ * flare p R (Lattice.gauge k U) * trench k=flare p R U := by
    rw [trench,flare, ← damage_rate, burn_carry k hp U]; rfl; exact he
end comparison
section borne
variable (h : S.patch.Branches S.kernel G) (t : S.Choices) (k : Coats G f) (u : Coats G c) (U : Joint G c f) (V W : Config G c)
    {p : Clip} {R : PathData G} {μ σ A Λ : ℝ} (he : R.Bounds p σ A Λ)

lemma endure : inure S (Lattice.gauge u V) (Lattice.gauge u W) ∘ (armor u)= inure S V W := by
  funext x; simp only [Function.comp_apply,inure,armor_go,tickets]
  congr 1; apply Finset.sum_congr rfl; intro i _
  have hp := G.price_conj (u i.1) (V i*((input G c x*W) i)⁻¹)
  refine Eq.trans (congr_arg G.price ?_) hp
  unfold Lattice.gauge; group

include h
lemma quota_m (hz : Teller S t p R 1 U)
    (hb : Teller S t p R 1 (wages S k u U)) :
    quota S t 1 (wages S k u U) * tactics k u=trench u* quota S t 1 U := by
  have he := rate_transfer (helmets G c f) (pocket (Lines G c 1)) _ _ (quota_k h t k u U hz) hb.wist hz.wist
  unfold quota tactics trench
  exact he
lemma damage_m : (trench u)ᵀ*damageC S t 1 (Lattice.gauge u V) (wages S k u U) * trench u=damageC S t 1 V U := by
  unfold damageC; rw [dress_one,dress_one,ribbons S t h,trench, ← damage_rate,endure]; exact teller_fee ..
include he
lemma legion_law (hp : Explosives S t 1 U) (hw : Explosives S t 1 (wages S k u U)) (ht : 0<μ) (hz : Teller S t p R 1 U)
    (hb : Teller S t p R 1 (wages S k u U)) :
    (tactics k u)ᵀ*legion S t p R μ 1 (Lattice.gauge u V) (wages S k u U)*tactics k u=legion S t p R μ 1 V U := by
  have hm := choir (rear_tactics k u) (flare_carry k he U.1 (show ContDiffAt ℝ ω (burn p R (Lattice.gauge k U.1)) 0 from hb.known))
  have hl := choir (quota_m h t k u U hz hb) (damage_m h t k u U V)
  unfold legion; simp only [Matrix.mul_add,Matrix.add_mul]
  exact congr_arg₂ _ (congr_arg₂ _ hm hl) (gear_honors h t k u U hp hw ht)
end borne
end YM.Stationary
end

/-!
# Signed symmetry transport of the FULL stationary determinant. Turning a link
around sends its increment by `-Ad_{U^{-1}}`, not just sign. Γ and N use
actual transformed tangent. The comparison fine regulator on initial-site
positive links isn't asserted covariant under all of this group.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

variable (s : Signed)

-- only origin pull needed for these symmetries

def raid (k : Coats G n) : Coats G n := k ∘ (s.act (R:=Per n))
def switchM : BaseSites G n →L[ℝ] BaseSites G n := gaugeColor.symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (φ:=fun _ : Site n => G.Color) (s.act i)) ∘L gaugeColor.toContinuousLinearMap
lemma rewind (x : BaseSites G n) (i) : gaugeColor (switchM s x) i=gaugeColor x (s.act i) := by simp [switchM]

def spiral (U : Config G n) : Link G n →L[ℝ] Link G n :=
    edgeColor.symm.toContinuousLinearMap ∘L (ContinuousLinearMap.pi (fun i : Edge (Site n) =>
      let j := sendEdge s 0 i
      let P := ContinuousLinearMap.proj (φ:=fun _ : Edge (Site n) => G.Color) (R:=ℝ) j
      if s.flip i.2 then - ((G.adjoint (U j)⁻¹).toContinuousLinearMap ∘L P) else P)) ∘L edgeColor.toContinuousLinearMap
lemma rotate_color (U : Config G n) (x : Link G n) (i) : edgeColor (spiral s U x) i=
    let j := sendEdge s 0 i
    if s.flip i.2 then - G.adjoint (U j)⁻¹ (edgeColor x j) else edgeColor x j := by
  cases h : s.flip i.2 <;> simp [spiral,h]
lemma rerun (U : Config G n) (e) : pull s 0 U e=if s.flip e.2 then (U (sendEdge s 0 e))⁻¹ else U (sendEdge s 0 e) := by
  simp [sendEdge,pull,Step.read,Step.rotate,posDir]
lemma wheel (U : Config G n) (x : Link G n) : pull s 0 (input _ _ x*U) = input _ _ (spiral s U x)*pull s 0 U := by
  funext i; rw [rerun]; simp only [Pi.mul_apply,rerun,input_color,rotate_color]; split; swap; rfl
  rw [Work.F03.exp_neg_color,adjoint_exp]; group

lemma circlings (U : Config G n) (x : BaseSites G n) : cant (pull s 0 U) (switchM s x)=spiral s U (cant U x) := by
  apply edgeColor.injective; funext i
  let j := sendEdge (n:=n) s 0 i
  rw [cant_at,rotate_color]; cases h : s.flip i.2
  · have hj : j=(s.act i.1, s.perm i.2) := by simp [j,sendEdge,Step.used,Step.rotate,posDir,h,affine]
    have ht : s.act (i.1+step i.2)=s.act i.1+step (s.perm i.2) := by simpa [affine] using StepData.possite s 0 i.1 i.2 h
    simp only [Bool.false_eq_true, ↓reduceIte,rerun, h, rewind,cant_at,show sendEdge s 0 i=_ from hj,ht]
  have hj : j=(s.act i.1-step (s.perm i.2), s.perm i.2) := by simp [j,sendEdge,Step.used,Step.rotate,posDir,h,affine]
  have ht : s.act (i.1+step i.2)=s.act i.1-step (s.perm i.2) := by simpa [affine] using StepData.negsite s 0 i.1 i.2 h
  simp only [↓reduceIte,rerun, h, rewind,cant_at,show sendEdge s 0 i=_ from hj,ht]
  rw [sub_add_cancel,map_sub,← G.adjoint_mul, inv_mul_cancel,G.adjoint_one,neg_sub]

def regimentG (G : Gauge) (n : Side) := billsM (pocket _) (pocket _) (switchM s (G:=G) (n:=n))
def regimentU (U : Config G n) := billsM (pocket _) (pocket _) (spiral s U)
lemma swirl (U : Config G n) : mail (pull s 0 U)*regimentG s G n=regimentU s U *mail U := testers fun i j => by simp only [← mulVec_mulVec,mailed,regimentG,regimentU,bill_pay,circlings]

lemma brigade_core (x y : BaseSites G n) : dotProduct (switchM s x) (switchM s y)=dotProduct x y := by
  rw [dotCoat,dotCoat]; simp_rw [rewind]; exact Equiv.sum_comp (s.actEquiv (R:=Per n)).toEquiv (fun i => inner ℝ (gaugeColor x i) (gaugeColor y i))
lemma bridle_core (U : Config G n) (x y : Link G n) : dotProduct (spiral s U x) (spiral s U y)=dotProduct x y := by
  rw [dotEdge,dotEdge]; conv_rhs => rw [← Equiv.sum_comp (StepData.sendBonds s (0:Site n))]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [rotate_color]; split; swap; rfl
  rw [inner_neg_neg]; exact (show G.Color →ₗᵢ[ℝ] G.Color from ⟨G.adjoint _, G.norm_adjoint _⟩).inner_map_map _ _
lemma brigade : Military (regimentG s G n) := military_intro _ (fun i j => by rw [regimentG,bill_pay,bill_pay,brigade_core])
lemma bridle (U : Config G n) : Military (regimentU s U) := military_intro _ (fun i j => by rw [regimentU,bill_pay,bill_pay,bridle_core])

def regiment (U : Joint G c f) : Vault G c f →L[ℝ] Vault G c f := (spiral s U.1).prodMap (switchM s)
def twistUniform (U : Joint G c f) : Joint G c f := (pull s 0 U.1,raid s U.2)
def fleetM (U : Joint G c f) := billsM (helmets _ _ _) (helmets _ _ _) (regiment s U)
lemma brigade_air (U : Joint G c f) : Military (fleetM s U) := by
  apply military_intro; intro x y
  obtain ⟨x,rfl⟩ := (cash (helmets G c f)).surjective x; obtain ⟨y,rfl⟩ := (cash (helmets G c f)).surjective y
  simp_rw [fleetM,bill_at,vault_bill]; change dotProduct (spiral s U.1 x.1) (spiral s U.1 y.1) + dotProduct (switchM s x.2) (switchM s y.2) = _; rw [brigade_core,bridle_core]
lemma fleet_act (U : Joint G c f) (x : Vault G c f) :
    twistUniform s (Stationary.extend x*U)=Stationary.extend (regiment s U x) * twistUniform s U := by
  refine Prod.ext (wheel s U.1 x.1) ?_
  funext i
  change switchSite x.2 (s.act i)*_=switchSite (switchM s x.2) i*U.2 (s.act i); rw [switch_color,switch_color,rewind]
lemma fleet_rear (U : Joint G c f) : rearM G c f*fleetM s U=regimentU s U.1*rearM G c f := by
  apply bill_eq (helmets G c f); intro x
  simp_rw [← Matrix.mulVec_mulVec,fleetM,bill_at, rear_cost,regimentU,bill_pay]; rfl

lemma stationed_twist {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U : X → Joint G c f} {x} (h : Thaw U x) : Thaw (fun z => twistUniform s (U z)) x := by
  refine ⟨fun i => ?_,fun _ => h.2 _⟩
  simp only [twistUniform,rerun]; split; · exact h.1.inv _
  exact h.1 _
@[simp] lemma twistUniform_one : twistUniform s (1: Joint G c f)=1 := by
  refine Prod.ext ?_ rfl; funext i; change pull s 0 _ _=_; simp [rerun]

variable (t : S.Choices) (h : S.patch.Branches S.kernel G)
include h
lemma curled (U : Joint G c f) :
    ribbon S t (twistUniform s U)=pull s 0 (ribbon S (S.withinChoice s 0 t) U) := by
  have he := S.prediction_channel h s 0 U.1 t
  rw [show S.ratio.embed 0=0 from map_zero S.ratio.root] at he
  simp only [ribbon,twistUniform,he, Work.F05.pull_gauge_zero,affine,add_zero]; rfl
lemma across_s (U : Joint G c f) : shield S t (twistUniform s U)=raid s (shield S (S.withinChoice s 0 t) U) := by
  have hj i := S.frames_match h s 0 U.1 t.1 i
  funext i
  have hv : hatPoint S (s.act i)=S.patch.offset s (hatPoint S i) := by
    apply Subtype.ext
    rw [Patch.coord,show (hatPoint S (s.act i)).val= Lattice.lift (S.ratio.residue (s.act i)) from rfl]
    have he : S.ratio.residue (s.act i)=s.act (S.ratio.residue i) := by
      obtain ⟨⟨x,y⟩,rfl⟩ := S.ratio.assemble_bijective.2 i
      rw [← S.ratio.assemble_signed S.patch.odd_side,Ratio.assemble_res,Ratio.assemble_res]
    rw [he, Ratio.lift_signed_of_odd]; rfl; exact S.patch.odd_side
  simp_rw [affine,add_zero, show S.ratio.embed 0=0 from map_zero S.ratio.root] at hj
  simp only [shield,twistUniform,raid,Function.comp_apply,hj,hv,Ratio.parent_signed S.ratio S.patch.odd_side]; rfl
lemma rocket_s (U : Joint G c f) : rocket S t 1 (twistUniform s U) ∘ regiment s U=switchM s ∘ rocket S (S.withinChoice s 0 t) 1 U := by
  funext x; simp only [Function.comp_apply,rocket,atire,dress_one, ← fleet_act s, across_s s t h,map_neg]
  congr 1

-- score comparison
lemma muster_spin (V : Config G c) (U : Joint G c f) (p : Clip) (R : PathData G) :
    muster S t p R (pull s 0 V) (twistUniform s U) = muster S (S.withinChoice s 0 t) p R V U := by
  rw [muster,curled s t h,muster]; refine congr_arg₂ _ ?_ ?_
  · exact orbit_axis (fun U : Config G f => quadratic p R U + uncut R.cubic U + uncut R.quartic U) U.1 s
  let Z := ribbon S (S.withinChoice s 0 t) U
  unfold tickets; apply congr_arg (S.kernel.penalty * ·); conv_rhs => rw [← Equiv.sum_comp (StepData.sendBonds s (0:Site c))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rerun,rerun]; split; swap; rfl
  have he (x y : G.El) : G.price (x⁻¹*(y⁻¹)⁻¹)=G.price (x*y⁻¹) := by
    rw [← G.price_inv (x*y⁻¹), show (x*y⁻¹)⁻¹=x*(x⁻¹*(y⁻¹)⁻¹)*x⁻¹ by group,G.price_conj]
  exact he ..
lemma troop_turn (V : Config G c) (U : Joint G c f) (p : Clip) (R : PathData G) :
    canon S t p R (pull s 0 V) (twistUniform s U) ∘ (regiment s U) = canon S (S.withinChoice s 0 t) p R V U := by
  funext x; simp only [Function.comp_apply,canon,← fleet_act,muster_spin s t h]
lemma sail {p : Clip} {R : PathData G} (V : Config G c) (U : Joint G c f) (hp : Shell S (S.withinChoice s 0 t) p R V U) :
    Shell S t p R (pull s 0 V) (twistUniform s U) := by
  let F := canon S t p R (pull s 0 V) (twistUniform s U)
  let H := canon S (S.withinChoice s 0 t) p R V U
  let M := regiment s U
  have hi : IsUnit M.toLinearMap := (LinearMap.isUnit_toMatrix_iff _).1 (brigade_air s U).unit
  obtain ⟨T,hT⟩ := hi
  let B := LinearMap.toContinuousLinearMap ((T⁻¹).val)
  have he : F=H∘B := by
    rw [show H = F∘M from (troop_turn s t h V U p R).symm]; funext x
    have ht : M (B x)=x := by
      change M.toLinearMap ((T⁻¹).val x) = x; rw [← hT, ← Module.End.mul_apply,Units.mul_inv]; rfl
    simp only [Function.comp_apply,ht]
  have hh : ContDiffAt ℝ ω H (B 0) := by rw [map_zero]; exact hp.1
  change ContDiffAt ℝ ω F _ ∧ fderiv ℝ F _=_
  rw [he]; refine ⟨hh.comp _ B.contDiff.contDiffAt,?_⟩
  rw [fderiv_comp _ (hh.differentiableAt (by simp)) B.differentiableAt,map_zero, show fderiv ℝ H 0=0 from hp.2, ContinuousLinearMap.zero_comp]

lemma twistWorth (V : Config G c) (U : Joint G c f) (p : Clip) (R : PathData G) (μ : ℝ) (hv : 0<μ)
    (ht : Explosives S (S.withinChoice s 0 t) 1 U) (hk : Explosives S t 1 (twistUniform s U))
    (hp : Shell S t p R (pull s 0 V) (twistUniform s U)) :
    bounty S p R μ t 1 (pull s 0 V) (twistUniform s U)= bounty S p R μ (S.withinChoice s 0 t) 1 V U := by
  let Q := S.withinChoice s 0 t
  let X := twistUniform s U
  have he := artillery U.1 hv (pull s 0 U.1) (brigade s) (bridle s _) (swirl s _)
  have hu : indexX S t 1 X *fleetM s U=regimentG s G f*indexX S Q 1 U := by
    have hi := rate_transfer (helmets G c f) (pocket (Lines G f 0)) _ _ (EventuallyEq.of_eq (rocket_s s t h U)) (market S t 1 _ hk) (market S Q 1 _ ht)
    exact hi
  have hx : cannonade S t μ 1 X * fleetM s U=regimentG s G f*cannonade S Q μ 1 U := by
    rw [cannonade,Matrix.add_mul,Matrix.mul_assoc _,fleet_rear, ← Matrix.mul_assoc,show X.1=_ from (show X.1=pull s 0 U.1 from rfl), (brigade s).transpose_cross (bridle s _) (swirl s _),cannonade,Matrix.mul_add]
    rw [Matrix.mul_assoc (regimentG s G f),Matrix.mul_assoc (cannon μ _),hu,← Matrix.mul_assoc (cannon μ _),he.1,Matrix.mul_assoc]
  have hg : (fleetM s U)ᵀ*medals S t p R μ 1 (pull s 0 V) X*fleetM s U=medals S Q p R μ 1 V U := by
    rw [medals,medals,cannon_law,cannon_law,Matrix.mul_add,Matrix.add_mul]
    exact congr_arg₂ _ ((damage_rate _ (helmets G c f) _ (regiment s U) (show ContDiffAt ℝ ω (canon S t p R (pull s 0 V) (twistUniform s U)) 0 from hp.1)).symm.trans (by rw [troop_turn s t h])) (gram_bend _ _ _ (brigade s) hx)
  exact congr_arg₂ (fun x y => _*Real.log x - Real.log y) ((brigade_air s U).turn_det hg) ((brigade s).turn_det ((brigade s).back he.2))
end YM.Stationary
end

/-!
# Compare fees under exact station reduction along any (origin) parameter probes.
Tag choices held, and both input loop and full bounty obey *signed* symmetry on-shell.
Combined source of the real lattice Ward checks for actual output jets.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Matrix Module
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio}

section render
variable (t : S.Choices) (μ : ℝ) (p : Clip) (R : PathData G) (F) (ρ : Bid.Dir G c → AxisChart G F)
def victory (x : Link G c) := tested F t p R (arm _ _ _ x) (ρ (arm _ _ _ x))
def honorarium (x : Link G c) := bounty S p R μ t 1 (input G c x) (encamp F ρ x)
def burnished (x : Link G c) := Precision.loop R (encamp F ρ x).1
end render

section
-- Along Probe (parameterized) not identifying near with quotient representative until stationary
variable {p : Clip} {R : PathData G} {μ σ A Λ b : ℝ} {ρ : Bid.Dir G c → AxisChart G F}
variable (hc : Critical F p R ρ) (h : S.patch.Branches S.kernel G) (hp : R.Bounds p σ A Λ) (t r : S.Choices)
    (hv : PriceGap F p R b) (hb : 0<b) (hy : 0<μ) {C : ChartRatio G} (hC : LocalRatio C)
include hc h hp hv hb hy
section law

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [CompleteSpace X]
    {B D : X → Link G c} {U : X → Joint G c f}

lemma tribute_probe (hi : Thaw U 0) (he : U 0=1) (ha : ContDiffAt ℝ ω B 0) (hd : B 0=0)
    (hs : ∀ᶠ x in 𝓝 0, Shell S t p R (input G c (B x)) (U x)) :
    ∀ᶠ x in 𝓝 0, victory F t p R ρ (B x)=muster S t p R (input G c (B x)) (U x) ∧
      honorarium F t μ p R ρ (B x)= bounty S p R μ t 1 (input G c (B x)) (U x) ∧
      burnished F R ρ (B x)=Precision.loop R (U x).1 := by
  have hi' := veterans hc h hp hv hb t hi he ha hd hs
  have he' (x₀) : (wages S (boots S F (U x₀)) 1 (U x₀)).1 = Lattice.gauge (boots S F (U x₀)) (U x₀).1 := rfl
  filter_upwards [hi', explosive S t h root_customs hi (by rw [he]; rfl),explosive S t h root_customs (cloak_lit S F hi) (by rw [he,cloak_zero S F]; rfl),hs] with x hx hy' H hG
  have hb' := bounty_carry h t (boots S F (U x)) 1 (U x) (input G c (B x)) hp hy' H hy
    (hG.wage h hp (boots S F (U x)) 1).1
  rw [gauge_one] at hb'
  have hh := root_wages S t h (U x) 1 (boots S F (U x)) p R hp (input G c (B x)); rw [gauge_one] at hh
  rw [victory,← camp_claim,honorarium,burnished,← hx]
  exact ⟨hh,hb',Work.F05.loop_gauge hp ..⟩

lemma tribute_wager (ha : ContDiffAt ℝ ω B 0) (hd : B 0=0) (hl : ContDiffAt ℝ ω D 0) (hg : D 0=0)
    {k : X → Coats G f} {u : X → Coats G c}
    (he : U = fun x => wages S (k x) (u x) (encamp F ρ (B x))) (hi : Thaw U 0) (hu : U 0=1)
    (hz : ∀ᶠ x in 𝓝 0, input G c (D x)=Lattice.gauge (u x) (input G c (B x))) :
    ∀ᶠ x in 𝓝 0, victory F t p R ρ (D x)= victory F t p R ρ (B x) ∧ honorarium F t μ p R ρ (D x)=honorarium F t μ p R ρ (B x) ∧ burnished F R ρ (D x)=burnished F R ρ (B x) := by
  have hr := camp_station hc h hp t
  have ht : Tendsto B _ (𝓝 0) := hd ▸ ha.continuousAt.tendsto
  have he' : ∀ᶠ x in 𝓝 0, Shell S t p R (input G c (D x)) (U x) := by
    filter_upwards [ht.eventually hr,hz] with x hx hv; rw [hv,congr_fun he x]; exact hx.wage h hp _ _
  have hh := ht.eventually (explosive S t h root_customs (camp_thaw hc) (by rw [encamp_zero hc]; rfl))
  have ho := explosive S t h root_customs hi (by rw [hu]; rfl)
  filter_upwards [tribute_probe hc h hp t hv hb hy hi hu hl hg he', he',ho,hz, hh] with x hx hX hY hw hG
  rw [hw,congr_fun he x] at hx hX; rw [congr_fun he x] at hY
  refine ⟨hx.1.trans ?_,hx.2.1.trans ?_,hx.2.2.trans ?_⟩
  · rw [root_wages S t h _ _ _ _ _ hp]; exact camp_claim ..
  · unfold honorarium
    exact bounty_carry h t _ _ _ _ hp hG hY hy hX.1
  exact Work.F05.loop_gauge hp ..

end law

include hC
lemma coin_tag : (victory F t p R ρ)=ᶠ[𝓝 0] (victory F r p R ρ) ∧
    (honorarium F t μ p R ρ)=ᶠ[𝓝 0] (honorarium F r μ p R ρ) := by
  let K := arm G c 1
  have hp' : Tendsto K (𝓝 0) (𝓝 0) := by unfold K; simpa using (arm G c 1).continuous.tendsto 0
  have ht := Work.F04.tested_germ h F p R t r
  have hh := (Work.F05.crit_home hc).comp hp'
  refine ⟨hh.eventually ht,?_⟩
  filter_upwards [hp'.eventually ((Work.F05.crit_home hc).eventually (eventually_eventually_nhds.mpr ht)), tribute hc h hp hv hb hy t hC, tribute hc h hp hv hb hy r hC] with a hw hx hA
  apply add_left_cancel (a:=Precision.loop R (encamp F ρ a).1)
  have he : thermal F t p R ρ C (K a)=thermal F r p R ρ C (K a) := by
    let f := tested F t p R
    let g := tested F r p R
    have hu : f (K a)=ᶠ[𝓝 (ρ (K a))] g (K a) := Work.F05.hold_near (x:=K a) (y:=ρ (K a)) hw
    simp only [thermal,hessian,show iteratedFDeriv ℝ 2 (tested F t p R (K a)) (ρ (K a))= _ from (hu.iteratedFDeriv ℝ 2).eq_of_nhds]; rfl
  exact hx.2.symm.trans (he.trans hA.2)

lemma turn_tribute (s : Signed) :
    ∀ᶠ z in 𝓝 0, victory F t p R ρ (orderTurn s z) = victory F t p R ρ z ∧
      honorarium F t μ p R ρ (orderTurn s z) = honorarium F t μ p R ρ z ∧
      burnished F R ρ (orderTurn s z)=burnished F R ρ z := by
  let A := orderTurn s (G:=G) (m:=c)
  let r := S.withinChoice s 0 t
  let U z := twistUniform s (encamp F ρ z)
  have he : Thaw U 0 := stationed_twist s (camp_thaw hc)
  have hu : U 0=1 := by simp [U, encamp_zero hc]
  have hz (x) : input G c (A x)=pull s 0 (input G c x) := (flip_links s x).symm
  have hs : ∀ᶠ z in 𝓝 0, Shell S t p R (input G c (A z)) (U z) := by
    filter_upwards [camp_station hc h hp r] with z ht; rw [hz]; exact sail s t h (input G c z) (encamp F ρ z) ht
  obtain ⟨H,H'⟩ := coin_tag hc h hp t r hv hb hy hC
  filter_upwards [H,H',tribute_probe (B:=A) hc h hp t hv hb hy he hu A.contDiff.contDiffAt (map_zero _) hs,
    hs,explosive S r h root_customs (camp_thaw hc) (by rw [encamp_zero hc]; rfl), explosive S t h root_customs he (by rw [hu]; rfl)] with x ht hT he hs hv hw
  change Shell _ _ _ _ _ (U x) at hs
  rw [hz] at hs he
  rw [ht,hT]
  refine ⟨he.1.trans ?_,he.2.1.trans ?_,he.2.2.trans ?_⟩
  · unfold U; rw [muster_spin s t h]; exact camp_claim ..
  · exact twistWorth s t h _ _ _ _ μ hy hv hw hs
  exact orbit_axis (uncut R.loop) (encamp F ρ x).1 s

omit hC in
lemma gauge_tribute (u : G.El) : ∀ᶠ z in 𝓝 0, victory F t p R ρ (stain u z)=victory F t p R ρ z ∧
      honorarium F t μ p R ρ (stain u z)=honorarium F t μ p R ρ z ∧
      burnished F R ρ (stain u z)=burnished F R ρ z := by
  let A := stain (m:=c) u
  let k (_ : Link G c) (_ : Site f) := u
  let U (_ : Link G c) (_ : Site c) := u
  apply tribute_wager hc h hp t hv hb hy (B:=fun i => i) (D:=A) contDiffAt_id rfl A.contDiff.contDiffAt (map_zero _) (u:=U) (k:=k) rfl
    ((camp_thaw hc).wages S (Army.park _ _) (Army.park _ _)) _ (Eventually.of_forall fun z => (stain_cons u z).symm)
  ext i <;> simp [wages,Lattice.gauge,U,k, encamp_zero hc]

omit hC in
lemma tested_forced : ∀ᶠ z : Swatch G c in 𝓝 0, victory F t p R ρ (moveField z)= victory F t p R ρ z.2 ∧ honorarium F t μ p R ρ (moveField z)=honorarium F t μ p R ρ z.2 ∧ burnished F R ρ (moveField z)= burnished F R ρ z.2 := by
  let Z := fun p : Swatch G c => switchSite p.1
  let A := moveField (G:=G) (m:=c)
  refine tribute_wager hc h hp t hv hb hy (X:=Swatch G c) (B:=Prod.snd) (D:=A) contDiffAt_snd rfl moveField_analytic.contDiffAt moveField_zero (k:=fun _ => 1) (u:=Z) rfl
    ((Thaw.comp (w:=Prod.snd) (g:=encamp F ρ) (camp_thaw hc) (x:=0) contDiffAt_snd).wages S (Army.park _ _) (Army.powG (v:=Prod.fst) contDiffAt_fst)) ?_ moveField_germ
  exact (show wages S 1 (Z 0) (encamp F ρ 0)=1 by rw [show Z 0=1 from switch_zero,wages_zero,encamp_zero hc])

lemma campaign : Pointwise (victory F t p R ρ) ∧ Pointwise (honorarium F t μ p R ρ) ∧ Pointwise (burnished F R ρ) := by
  have hd := camp_thaw hc
  have hm : Army (input G c) 0 := Army.powL contDiffAt_id
  have hc' : encamp F ρ 0=1 := encamp_zero hc
  obtain h0 := turn_tribute hc h hp t hv hb hy hC
  obtain h1 := gauge_tribute hc h hp t hv hb hy
  obtain h2 := tested_forced hc h hp t hv hb hy
  have hX := ammo_pay _ _ hd (by rw [hc']; rfl) hm 1 root_customs h t hp hy
  refine ⟨⟨?_,fun i => (h0 i).mono fun _ H => H.1,fun i => (h1 i).mono fun _ H => H.1, h2.mono fun _ H => H.1⟩,
    ⟨?_,fun i => (h0 i).mono fun _ H => H.2.1,fun i => (h1 i).mono fun _ H => H.2.1,h2.mono fun _ H => H.2.1⟩,
    ⟨?_,fun i => (h0 i).mono fun _ H => H.2.2,fun i => (h1 i).mono fun _ H => H.2.2,h2.mono fun _ H => H.2.2⟩⟩
  · have hi := hd.earn h t (show (encamp F ρ 0).1=1 from congrArg Prod.fst hc') hm hp
    simp_rw [camp_claim] at hi; exact hi.analyticAt
  · have H := (memo_flash hy hd.1).2.2
    have he := (tribute hc h hp hv hb hy t hC).self_of_nhds.1
    exact (ContDiffAt.sub (ContDiffAt.mul contDiffAt_const ((Memo.det_val hX.2.1).log he.ne')) ((Memo.det_val H).log (grenade_safe _ hy).det_pos.ne')).analyticAt
  apply ContDiffAt.analyticAt
  unfold burnished Precision.loop Patch.average
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun i _ => ?_)
  exact Work.F02.uncut_contDiffAt (A:=fun z => pull i 0 (encamp F ρ z).1) hp.width hp.two (stationed_twist i hd).1
end
end YM.Stationary
end
