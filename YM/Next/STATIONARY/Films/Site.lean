import YM.Next.STATIONARY.Spectral.AuxReferences
import YM.Work.B13



set_option autoImplicit false
/-!
# Half-derivative turns in mass graph. Uniform in volumes on both legs, incl
nonreal beams.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {L : Side} {p q : Momentum} {G : Gauge} {S : Patch} {C σ : ℝ}

lemma serial_basic {A : CompM α β} {C p q} (h : vflux A≤C) : serial (Slab.basic α) (Slab.basic β) p q A C := by simpa [serial,carryM,Slab.basic] using h

lemma rear_price (F : Momentum→ CompM α β) (h : 0≤C) (hp : p∈strip (1:ℝ)) (hv : ∀ i : Site L,vflux (F (aliasAt p i)) ≤ hill p i*C) : serial (Slab.basic _) (altarTile L β) p p (furnish L F p) (Real.exp 4*C) := by
  let c l := (hill p (l : Site L):ℂ)⁻¹ • F (aliasAt p l)
  have he : posterBlock L F p*diagonal (spice L β p)=fiber c := by ext ⟨i,a⟩ ⟨j,b⟩; rw [Matrix.mul_diagonal]; unfold posterBlock fiber; by_cases h : i=j <;> simp [*, c, spice,fiber,mul_comm]
  have ht : vflux (fiber c) ≤ C := by
    apply poster_flux h; intro i; unfold c; rw [flux_cost,norm_inv,Complex.norm_real,Real.norm_of_nonneg (hill_pos _ _).le, inv_mul_eq_div,div_le_iff₀ (hill_pos _ _)]; exact (hv _).trans_eq (mul_comm ..)
  unfold serial carryM Slab.basic altarTile contour furnish; simp only [id_eq, inv_one, Matrix.one_mul]
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (plankTile L β p)⁻¹, Matrix.nonsing_inv_mul _ (tile_solid _),Matrix.one_mul,← Matrix.mul_assoc (posterBlock L F p),he, ← Matrix.mul_assoc,(tile_ice (by simp : star (0:Momentum)=0)).back.slide_v]
  refine (flux_power ..).trans (mul_le_mul ?_ ht (flux_nonneg _) (Real.exp_pos _).le)
  simpa only [one_mul] using plank_cap p hp
lemma helm_price (F : Momentum→ CompM α β) (h : 0≤C) (hp : p∈strip (1:ℝ)) (hv : ∀ i : Site L,vflux (F (aliasAt p i)) ≤ hill p i*C) : serial (altarTile L α).dual (Slab.basic _) p p (furnish L F p) (C*Real.exp 4) := by
  let c l := (hill p (l : Site L):ℂ)⁻¹ • F (aliasAt p l)
  have he : diagonal (spice L α p)*posterBlock L F p=fiber c := by ext ⟨i,a⟩ ⟨j,b⟩; rw [Matrix.diagonal_mul]; unfold posterBlock fiber; by_cases h : i=j <;> simp [*, c, spice,fiber]
  have ht : vflux (fiber c) ≤ C := by
    apply poster_flux h; intro i; unfold c; rw [flux_cost,norm_inv,Complex.norm_real,Real.norm_of_nonneg (hill_pos _ _).le, inv_mul_eq_div,div_le_iff₀ (hill_pos _ _)]; exact (hv _).trans_eq (mul_comm ..)
  let H := (plankTile L α 0)⁻¹
  have hh : Skates H := (tile_ice (by simp)).back
  have hT : Skates Hᵀ := by have he := congr_arg Matrix.transpose (mul_eq_one_comm.mp hh.slides); rw [transpose_mul,Matrix.transpose_one] at he; exact ⟨he⟩
  unfold serial carryM; rw [Slab.inverse_dual]; unfold Slab.basic altarTile contour furnish; simp only [id_eq, Matrix.mul_one, Matrix.transpose_mul,pivot_left,Matrix.diagonal_transpose]
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc (plankTile L α p)⁻¹, Matrix.nonsing_inv_mul _ (tile_solid _), Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),skate_diagonal, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),he, show ((plankTile L α 0)⁻¹)ᵀ=Hᵀ from rfl,hT.slide_u,skate_unit.slide_u]
  refine (flux_power ..).trans (mul_le_mul ht ?_ (flux_nonneg _) h)
  simpa only [one_mul] using plank_back p hp
lemma plankPrice (F : Momentum→CompM α β) (hp : p∈strip (1:ℝ)) (hc : 0 ≤ C) (he : ∀ i:Site L,vflux (F (aliasAt p i))≤C) : serial (Slab.basic (Co L α)) (Slab.basic _) p p (furnish L F p) (Real.exp 4*C*Real.exp 4) := by
  apply serial_basic; unfold furnish
  let a : ℝ := Real.exp 4
  have ht : 0≤ a := (Real.exp_pos _).le
  refine (flux_power ..).trans (mul_le_mul ((flux_power ..).trans (mul_le_mul (by simpa only [one_mul] using plank_cap p hp) (poster_flux hc he) (flux_nonneg _) ht)) (by simpa only [one_mul] using plank_back p hp) (flux_nonneg _) (mul_nonneg ht hc))

-- Mail1 W two separate charges. Page.furn Γ calculus.

section page
variable (G L)
def pageSmooth (i : ℕ) := Real.exp 4 * (5 * pageTax G i)
def pageOrd (i : ℕ) := Real.exp 4*(pageTax G i*(2*(Real.exp 1+1)))*Real.exp 4
variable {G L}
lemma pageTroop (L : Side) (p : Momentum) (i : ℕ) (hp : p∈strip 1) : serial (Slab.basic _) (altarTile L _) p p (furnish L (pageD G i) p) (pageSmooth G i) := rear_price _ (mul_nonneg (by norm_num) (mul_nonneg fest_pos (by norm_num))) hp (fun j => (cold_t G i j hp).1.trans_eq (by ring))
lemma pageFrame (L : Side) (p : Momentum) (i : ℕ) (hp : p∈strip 1) : serial (altarTile L _|>.dual) (Slab.basic _) p p (furnish L (pageD G i) p) (pageSmooth G i) := by
  rw [pageSmooth, mul_comm]; exact helm_price _ (mul_nonneg (by norm_num) (mul_nonneg fest_pos (by norm_num))) hp (fun j => (cold_t G i j hp).1.trans_eq (by ring))
lemma pageBase (L : Side) (p : Momentum) (i : ℕ) (hp : p∈strip 1) : serial (Slab.basic _) (Slab.basic _) p p (furnish L (pageD G i) p) (pageOrd G i) := by
  apply plankPrice _ hp (mul_nonneg (mul_nonneg fest_pos (by norm_num)) (by positivity)); intro j
  exact lightPage (fun k => ((alias_inside hp j) k).trans_le (mul_le_of_le_one_left zero_le_one (inch_le L))) i
end page
end YM.Stationary
end

/-! # Rough-leg first payments. Allows ℓ² mixed budgets. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {n : ℕ} {c f m L : Side} {p : Momentum} {σ C A : ℝ}

lemma color_flick (i : Axis) (u : Phase (Co L α)) :
    flick p i u=furnish L (fun p=> Exterior.q p i • (1:CompM α α)) p *ᵥ u := by
  rw [← alias_pack p u,map_sum,mulVec_sum]; refine sum_congr rfl fun j _=> ?_
  rw [furnish_gear,flick_tapes,Matrix.smul_mulVec,one_mulVec]; ext1 a; simp [tiled,mul_left_comm]
lemma flick_plank (i : Axis) (u : Phase (Co L α)) (h : p ∈ strip (1:ℝ)) (he : (altarTile L α).rate p u ≤ 1) :
    slug (flick p i u) ≤ Real.exp 4*5 := by
  let F := fun p : Momentum => Exterior.q p i • (1 : CompM α α)
  have hx j : vflux (F (aliasAt p (j:Site L))) ≤ hill p j*5 := by
    unfold F; rw [flux_cost]; refine (mul_le_of_le_one_right (norm_nonneg _) flux_one).trans ?_
    rw [mul_comm]; exact (slug_atom (Exterior.q _) _).trans (hill_tilt j h)
  rw [color_flick]
  have hh := Slab.serial_at (rear_price F (by norm_num) h hx) u; rw [Slab.basic_rate] at hh; exact hh.trans (mul_le_of_le_one_right (by positivity) he)

lemma lower_voice {u : Phase (Co L α)} (hp : p∈strip (1:ℝ)) (he : (altarTile L α).rate p u≤1)
    (l : List Axis) (h : l.length≤1) (j : α) :
    Hearing (balcony _) 1 (fun z : Site L => flight p l u (z,j)) (inch L^(1+l.length)*(Real.exp 4*5)) := by
  have ht : 0 < inch L := inch_pos _
  have hr := ratePocket hp he
  match l with
  | [] =>
    simp only [List.length_nil, add_zero,pow_one]
    apply Hearing.more (C:=inch L* Real.exp 4)
    · exact hr.softer (fun i => slug_atom (stackSlice i u) j)
    gcongr; have hk := Real.exp_pos 4; linarith
  | a::v =>
    simp only [List.length_cons] at h
    rw [show v=[] from List.length_eq_zero_iff.mp (by omega)]
    let S := flick p a u
    have H : (flight p [a]) u=S := rfl
    rw [H]; simp only [List.length_cons,List.length_nil,zero_add]; refine ⟨by positivity,by omega,fun _ => ?_,by omega⟩
    have h : ∑ i : Site L, ‖S (i,j)‖^2 ≤ slug S^2 := by rw [slug_slots]; exact sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (slug_atom (stackSlice i S) j) 2)
    have he' : (balcony _).weightedSum (fun i : Site L => ‖S (i,j)‖^2) = inch L^4*∑ i : Site L,‖S (i,j)‖^2 := by
      unfold Audience.weightedSum balcony inch; rw [mul_sum]; apply sum_congr rfl; intro i _; dsimp only; rw [site_card]; push_cast; rw [inv_pow]
    rw [he']; calc
      _ ≤ _ := (mul_le_mul_of_nonneg_left (h.trans (pow_le_pow_left₀ (slug_nonneg _) (flick_plank _ _ hp he) _)) (by positivity))
      _ = _ := by ring
end YM.Stationary
end

/-!
# Link rotation change in RR^* spectra. No damping for scatter into
 site launch, vertex Δ in standing link. C¹ width shiftless in q.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {c f L n : Side} {p : Momentum}
-- mail(1) plus δ * (root − mail(1))

def scattering (G : Gauge) (u : G.El) : Funds G.ColorIndex := of fun i j =>
    let v := (WithLp.toLp 2 (Pi.single j (1:ℝ)) : G.Color)
    (v-G.adjoint u v) i
lemma scattering_d (u : G.El) (x : G.Color) : (scattering G u)*ᵥ (WithLp.ofLp x)=WithLp.ofLp (x-G.adjoint u x) := by
  let T := (LinearEquiv.toContinuousLinearEquiv <| WithLp.linearEquiv 2 ℝ (Corn G.ColorIndex))
  let L := T.toContinuousLinearMap ∘L ((ContinuousLinearMap.id ℝ G.Color)-(G.adjoint u).toContinuousLinearMap) ∘L T.symm.toContinuousLinearMap
  have he : scattering G u=billsM (pocket _) (pocket _) L := by ext i j; rw [bill_def,cash_pocket, show pocket G.ColorIndex j=Pi.single j 1 from Pi.basisFun_apply _ _ j]; rfl
  rw [he,bill_pay]; rfl
lemma scattering_one (G : Gauge) : scattering G 1=0 := by ext; simp [scattering]

def motley (U : Config G n) : Funds (Lines G n 1) := of fun i j => if i.1=j.1 ∧ i.2.1=j.2.1 then
    scattering G (U (i.1,axisEquiv.symm i.2.1)) i.2.2 j.2.2 else 0

lemma colorful (U : Config G n) (x : Link G n) (i : Edge (Site n)) :
    edgeColor (motley U *ᵥ x) i=edgeColor x i-G.adjoint (U i) (edgeColor x i) := by
  ext a
  have he : WithLp.ofLp ((edgeColor x i)-G.adjoint (U i) (edgeColor x i)) a=_ := (congr_fun (scattering_d (U i) (edgeColor x i)) a).symm
  change (motley U*ᵥ x) (i.1,coord i.2,a)=_; rw [he]
  unfold Matrix.mulVec dotProduct; simp only [motley,Matrix.of_apply, Fintype.sum_prod_type,ite_mul]
  rw [sum_eq_single i.1, sum_eq_single (coord i.2)]
  · simp only [and_self,↓reduceIte, show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _]; rfl
  · intro b _ H; simp [Ne.symm H]
  · simp
  · intro b _ H; simp [Ne.symm H]
  simp

def restaged (G : Gauge) (n : Side) := ∑ i : Axis, (stagehand i G n)ᵀ
lemma bingo_sign (u a : Axis) (x : BaseSites G n) (i) (k) : ((stagehand a G n)ᵀ*ᵥ x) (i,coord u,k) = if u=a then x (i,vac,k) else 0 := by
  let Q := stagehand a G n
  let z : Link G n := Pi.single (i,coord u,k) 1
  rw [show (Qᵀ*ᵥ x) _= dotProduct z (Qᵀ*ᵥ x) from (single_one_dotProduct _ _).symm, transposes]
  rcases eq_or_ne u a with hh|hh
  · subst u; rw [if_pos rfl]; have he : Q*ᵥ z=Pi.single (i,vac,k) 1 := by
      ext1 t; rcases t with ⟨p,j,l⟩; rw [vac_only j]; simp [Q,bingo_pull, z,Pi.single_apply]
    rw [he,single_one_dotProduct]
  have hs : coord u ≠ coord a := axisEquiv.injective.ne hh
  rw [if_neg hh]; rw [show Q*ᵥ z=0 by ext1 p; simp [Q,bingo_pull,z,Pi.single_apply,Ne.symm hs],zero_dotProduct]
lemma stardirect (x : BaseSites G n) (i : Edge (Site n)) : edgeColor (restaged G n*ᵥ x) i=gaugeColor x i.1 := by
  ext a; unfold restaged; rw [Matrix.sum_mulVec]; change (∑ u : Axis,(stagehand u G n)ᵀ *ᵥ x) (i.1,coord i.2,a)= _; rw [Finset.sum_apply]; simp_rw [bingo_sign]; simp; rfl

def shiftLaunch (G : Gauge) (n : Side) := restaged G n-mail (1:Config G n)
lemma until_age (x : BaseSites G n) (i : Edge (Site n)) : edgeColor (shiftLaunch G n*ᵥ x) i=gaugeColor x (i.1+step i.2) := by rw [shiftLaunch, Matrix.sub_mulVec,map_sub,Pi.sub_apply, stardirect,mailed,cant_at,Pi.one_apply,G.adjoint_one]; abel
lemma vivid (U : Config G n) : mail U=mail (1:Config G n)+ motley U* shiftLaunch G n := by
  refine testers fun x y => ?_; rw [mailed, add_mulVec,mailed, ← Matrix.mulVec_mulVec]; apply congr_arg _; apply edgeColor.injective; ext1 i; rw [map_add,Pi.add_apply,colorful,until_age,cant_at,cant_at,Pi.one_apply,G.adjoint_one]; abel
end YM.Stationary
end

/-!
# Uniform film for motley changes. Includes real canvas size and zero. D¹
 rotates actual background; edge indexed with color slots. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {c f L n : Side} {p : Momentum} {m : ℕ} {K : KernelChoices} {σ C : ℝ}

def harpoon (P : Patch) (i : Site P.L) : Plaza P := ⟨lift i,alley (hatch P i)⟩
def canalBox (u v : Loc G 1) (a : Site P.L) (x : BassInput G P) := if u.1=v.1 then scattering G (G.lieExp (whipF false (harpoon P a) (axisEquiv.symm u.1) x)) u.2 v.2 else 0
def frameBrill (M : Eye ι (Acts G P)) : Leagues ι (Co P.L (Loc G 1)) (Co P.L (Loc G 1)) := fun n p i _ => fiber (fun a : Site P.L => of fun u v => beat (canalBox u v a) 0 n (lens (inviton M i p) p))
def Dapper (M : Eye ι (Acts G P)) := recitalX (frameBrill M)

section rates
lemma scat_rate (i j : G.ColorIndex) : ContDiffAt ℝ ω (fun u : G.Color => scattering G (G.lieExp u) i j) 0 := by
  let V := (WithLp.toLp 2 (Pi.single j (1:ℝ)):G.Color)
  have he : ∀ u, G.adjoint (G.lieExp u) V=G.projectColor (G.mat (G.lieExp u)*G.colorMat V*star (G.mat (G.lieExp u))) := fun u => by
    rfl
  have hh : ContDiffAt ℝ ω (fun u => G.adjoint (G.lieExp u) V) 0 := by
    simp_rw [he]; let F u := G.mat (G.lieExp u)
    have hp : ContDiffAt ℝ ω F 0 := G.exp_jet.contDiffAt
    apply G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=fun u => F u * G.colorMat V * star (F u)) _
    exact (hp.mul contDiffAt_const).mul ((show G.Mat≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ hp)
  obtain ⟨P,hP,hT⟩ := color_beak i
  change ContDiffAt ℝ ω (fun u => (V-G.adjoint (G.lieExp u) V) i) _; simp_rw [← hP]
  exact P.contDiff.contDiffAt.comp (g:=P) (f:=fun u => V-G.adjoint (G.lieExp u) V) _ (contDiffAt_const.sub hh)
lemma canal_diff (i j : Loc G 1) (a : Site P.L) : ContDiffAt ℝ ω (canalBox i j a) 0 := by
  unfold canalBox; split
  · let F := whipF (G:=G) (P:=P) false (harpoon P a) (axisEquiv.symm i.1)
    exact ((show ContDiffAt ℝ ω (fun u : G.Color => scattering G (G.lieExp u) i.2 j.2) (F 0) by rw [map_zero]; exact scat_rate ..).comp (f:=F) _ F.contDiff.contDiffAt)
  exact contDiffAt_const
end rates
section mesh
variable (S : StepData c f) (t : S.Choices)
lemma factorC_power (r : Bool) (x : Bang G c f) : (headOn S t r x).1=input G f x.1.2.1 := by cases r <;> rfl
lemma factorCG (x : Bang G c f) (a : Site c) (i : Site S.patch.L) (j : Axis) :
    whipF false (harpoon S.patch i) j (pianist S a x)=edgeColor x.1.2.1 (S.ratio.assemble (a,i),j) := by
  ext k
  change x.1.2.1 (wrap f (Lattice.lift i)+ S.ratio.embed a,coord j,k)=x.1.2.1 (_,coord j,k)
  rw [Ratio.assemble,add_comm _ (S.ratio.embed _)]; rfl
lemma canvas_in (x : Bang G c f) (r : Bool) (i j : Co c (Co S.patch.L (Loc G 1))) :
    repackM (unitSplit G S 1) (unitSplit G S 1) (motley (headOn S t r x).1) i j = if i.1=j.1 ∧ i.2.1=j.2.1 then canalBox i.2.2 j.2.2 i.2.1 (pianist S i.1 x) else 0 := by
  let T : Lines G f 1 ≃ Co c (Co S.patch.L (Loc G 1)) := unitSplit G S 1
  rcases i with ⟨i,u,k⟩; rcases j with ⟨j,v,l⟩
  have he i u k : T.symm (i,u,k)=(S.ratio.assemble (i,u),k) := by apply T.injective; rw [T.apply_symm_apply,show T (_,_)=((S.ratio.parent _ : Site c),_,k) from split_co .., S.ratio.assemble_parent,S.ratio.assemble_res]
  change motley _ (T.symm _) (T.symm _)=_
  rw [he i u k,he j v l]; unfold motley; simp only [Matrix.of_apply]
  have hp : S.ratio.assemble (i,u)=S.ratio.assemble (j,v) ↔ i=j ∧ u=v := by rw [S.ratio.assemble_bijective.injective.eq_iff]; exact Prod.mk.injEq .. ▸ Iff.rfl
  by_cases h : i=j ∧ u=v <;> simp only [hp,h,false_and, ↓reduceIte,true_and]
  unfold canalBox; split; next e => rw [factorC_power,input_color,factorCG S]
  rfl

variable (r : Bool) (Z : Corn (Co c ι)→L[ℝ] Bang G c f) {D : Eye ι (Acts G S.patch)}
theorem bending_ticket (h : Turns D (billZ S Z)) :
    Ticket (Dapper D) (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (motley (headOn S t r (Z x)).1)) := by
  classical
  let M : OperatorF ι c (Co S.patch.L (Loc G 1)) (Co S.patch.L (Loc G 1)) := fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (motley (headOn S t r (Z x)).1)
  let A := billZ S Z
  let K := Co c (Co S.patch.L (Loc G 1))
  let T := fun v a b => canalBox (P:=S.patch) (G:=G) a b v
  have ht i (u : Site S.patch.L) (a b) : AnalyticAt ℝ (T u a b ∘ rehearsal S i) 0 :=
      (ContDiffAt.comp (x:=(0:Corn (Co c (Acts G S.patch)))) (g:=T u a b) (f:=rehearsal S i) (by rw [map_zero]; exact canal_diff ..) ((rehearsal S i).contDiff.contDiffAt)).analyticAt
  have he (i j : K) x : M x i j= if i.1=j.1 ∧ i.2.1=j.2.1 then (T i.2.1 i.2.2 j.2.2 ∘ rehearsal S i.1) (A x) else 0 := by
    refine (canvas_in S t _ _ i j).trans ?_; rw [Function.comp_apply, show rehearsal S i.1 (A x)= _ from rehearsing S (Z x) i.1]
  refine all_ground (K:=frameBrill D) (M:=M) (fun i j => ?_) (fun n p i v hz q z hw w => ?_)
  · simp_rw [he i j]; split
    · exact (show ContDiffAt ℝ ω (T i.2.1 i.2.2 j.2.2 ∘ rehearsal S i.1) (A (0:_)) by rw [map_zero]; exact (ht ..).contDiffAt).comp _ A.contDiff.contDiffAt
    exact contDiffAt_const
  let R := fun j => relay (v j) (i j)
  let k := lens (inviton D i p) p
  obtain ⟨B,hB,hQ⟩ := h.basis
  have hy (x y : K) : art M n R x y= if x.1=y.1 ∧ x.2.1=y.2.1 then cell (∑ j,v j) x.1 * beat (T x.2.1 x.2.2 y.2.2) 0 n k else 0 := by
    unfold art; simp only [Matrix.of_apply]; simp_rw [he]; split; next e =>
      rw [show (fun a => (T x.2.1 x.2.2 y.2.2 ∘ rehearsal S x.1) (A a))= (T x.2.1 x.2.2 y.2.2 ∘ rehearsal S x.1) ∘ A from rfl,evaluated _ (fun x => (hB x).symm) (ht x.1 x.2.1 x.2.2 y.2.2),MultilinearMap.compLinearMap_apply,show (fun j => B (R j))=fun j => tune (v j) (inviton D i p j) from funext fun j => hQ (v j) (p j) (hz j) _]
      exact audition S v p hz (inviton D i p) x.1 _ (canal_diff .. |>.analyticAt)
    simp [beat,enlarge,recording_apply]
  ext1 x
  change (art M n R*ᵥ tune q w) x=tune _ _ x; simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type]
  simp_rw [hy]; unfold tune frameBrill; simp only [fiber,Matrix.of_apply]
  rcases x with ⟨x,a,b⟩; simp only [ite_mul,ite_and]; simp
  rw [cell_duality (q+_),cell_add,cell_duality x,cell_duality x]
  simp only [Matrix.mulVec, dotProduct,Fintype.sum_prod_type, Matrix.of_apply,ite_mul]
  simp [T,k]
  simp_rw [Finset.mul_sum]; refine sum_congr rfl fun i _ => ?_; refine sum_congr rfl fun j _ => ?_; ring
end mesh
end YM.Stationary
end

/-!
# Motley's diagonal pricing. Γ=RR* costs first regime by this.
No real cut assumptions.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {E : Eye ι (Acts G P)} {C σ : ℝ}

lemma Dapper.green (h : Fresh E σ) : Play (Dapper E) σ := by
  refine cosmic _ ?_ ?_
  · intro n p r i q z h1 h2 w1 w2 w3
    have he : lens (inviton E i p) p=lens (inviton E i r) r := by ext1 k; unfold lens inviton; rw [flips_melody _ (h1 k),h.shifts (h1 k) (w1 k)]
    simp only [frameBrill,he]
  intro X _ _ x n p q b w1 w2 w3 hP hQ i j
  unfold frameBrill fiber; simp only [Matrix.of_apply]; split
  · refine differentiableBeat (u:=fun z => lens (inviton E b (p z)) (p z)) (fun i => ?_) _
    exact melody_diff ((h.sense (w1 i) _).comp (f:=fun z => p z i) x (hP i)) (hP i)
  exact differentiableAt_const _
lemma Dapper.base : (Dapper E).tab=0 := by
  funext p; ext i j; unfold Dapper frameBrill recitalX; simp only [fiber,Matrix.of_apply]
  split; swap; exact rfl
  rw [show lens (inviton E ![] ![]) ![]=axes ∘ (![]:Fin 0→BassInput G P) from Subsingleton.elim ..,beat_real,iteratedFDeriv_zero_apply]; simp [canalBox,scattering_one]

-- PaCo budgets positive. actual period ℓ. Require for λ only staff.
def scatterCharge (G : Gauge) (n : ℕ) (C : ℝ) := ∑ i : G.ColorIndex,∑ j : G.ColorIndex, |encore (fun z : G.Color => scattering G (G.lieExp z) i j) 0 C n|
def dapperPrice (G : Gauge) (C : ℝ) (n : ℕ) := fest (Loc G 1) (Loc G 1)*((2:ℝ)^n*scatterCharge G n C)
lemma scattering_fare {C : ℝ} (h : 0≤C) (a : Site P.L) (n : ℕ) (p q : Loc G 1) : Gallop (balcony Unit)
    (fun v i => i=0 ∧ StaffP G P C v i) (fun _ => canalBox p q a) n (inch P.L*scatterCharge G n C) := by
  classical
  unfold canalBox
  by_cases ht : p.1=q.1
  · simp only [ht, ↓reduceIte]; let L := (whipF false (harpoon P a) (axisEquiv.symm q.1) : BassInput G P →L[ℝ] G.Color)
    have he : ContDiffAt ℝ ω (fun z : G.Color => scattering G (G.lieExp z) p.2 q.2) 0 := scat_rate _ _
    let R (v : BassInput G P) (k : ℕ) := k=0 ∧ StaffP G P C v k
    have hp : Gallop (balcony Unit) R (fun _ x => L x) n (inch P.L*C) := steelG R _ (fun i a hv => Hearing.sup (mul_nonneg (inch_pos _).le h)
      (fun _ => (hv.2.fly _ _).all hv.1 (harpoon P _))) (mul_nonneg (inch_pos _).le h) n
    apply (scaleG R hp (fun _ => L.map_zero) (inch_pos _).le (inch_le P.L) h he).raises le_rfl
    gcongr; · exact (inch_pos P.L).le
    let f i j := encore (fun z : G.Color => scattering G (G.lieExp z) i j) 0 C n
    apply le_trans (le_abs_self _) <| le_trans (single_le_sum (s:=univ) (f:=fun j => |f p.2 j|) (fun j _ => abs_nonneg _) (mem_univ q.2)) _
    exact single_le_sum (s:=univ) (f:=fun i => ∑ j,|f i j|) (fun _ _ => sum_nonneg (fun j _ => abs_nonneg _)) (mem_univ p.2)
  simp only [ht, ↓reduceIte]
  exact Gallop.goes _ (mul_nonneg (inch_pos P.L).le (Finset.sum_nonneg (s:=univ) (f:=fun i=> ∑ j, |encore (fun z : G.Color => scattering G (G.lieExp z) i j) 0 C n|) (fun j _ => sum_nonneg (fun i _ => abs_nonneg _))))

lemma Dapper.trails (h : Spotlight P E σ C) : Charges (Slab.basic _) (Slab.basic _) (Dapper E) σ
    (inch P.L * feeHead (dapperPrice G (muralRoom P.J*C))) := by
  classical
  have he := weight_staff h
  have h' := inch_pos P.L
  have hh n : 0 ≤ scatterCharge G n (muralRoom P.J*C) := by unfold scatterCharge; positivity
  have hx n : 0 ≤ dapperPrice G (muralRoom P.J*C) n := mul_nonneg fest_pos (mul_nonneg (by positivity) (hh n))
  refine serial_caps (green h.fresh) (fun n hn i v w p ht _ => ?_)
  refine serial.mono (A:=inch P.L*dapperPrice G (muralRoom P.J*C) n) ?_ (mul_le_mul_of_nonneg_left (fee_ge _ hn) (inch_pos _).le)
  unfold frameBrill
  rcases eq_or_ne n 0 with H|H
  · subst n
    have hs : i=![] := Subsingleton.elim ..; have hz : v=![] := Subsingleton.elim ..
    rw [hs,hz,show fiber _=(Dapper E).tab p from rfl,Dapper.base]; exact serial.flat.mono (mul_nonneg h'.le (hx _))
  apply serial_basic; refine poster_flux (mul_nonneg h'.le (hx n)) (fun j => ?_)
  unfold dapperPrice; rw [mul_left_comm]
  apply flux_fest _ (by positivity [hh n])
  intro q z
  let u := scatterCharge G n (muralRoom P.J*C)
  let f : Unit → BassInput G P → ℝ := fun _ => canalBox q z j
  let R (v : BassInput G P) (k : ℕ) := k=0∧ StaffP G P (muralRoom P.J*C) v k
  let L := lens (inviton E i v) v
  have hV := h.bright_lens v i w
  have hp k : Shiny R (L k) 0 := ⟨⟨rfl,(hV k).1⟩,⟨rfl,(hV k).2⟩⟩
  have hb := through_charge (scattering_fare he j n q z |>.reaches n (Nat.pos_iff_ne_zero.mpr H) le_rfl) (b:=fun _ => 0) hp (by simp)
  exact hb.all (by simp) () |>.trans_eq (by ring)
end YM.Stationary
end

/-!
# Orbit regulator Γ first legs. Matrix budgets both directions independently.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β ι γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] {G : Gauge} {c f L : Side} {P : Patch} {C D σ : ℝ} {p q : Momentum}
-- finite sum support
lemma Poster.tops (s : Finset γ) (F : γ→Momentum→CompM α β) (h : ∀ i∈s, Poster σ (F i)) : Poster σ (∑ i∈s,F i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [sum_empty]; exact Poster.web _
  | insert a s hs ih => rw [sum_insert hs]; exact Poster.amounts (h _ (by simp)) (ih fun i hi => h i (by simp [hi]))
lemma serial.tops (s : Finset γ) (F : γ →CompM α β) {k : γ→ℝ} {X : Slab α} {Y : Slab β} (h : ∀ i∈ s,serial X Y p q (F i) (k i)) : serial X Y p q (∑ i∈s,F i) (∑ i∈s, k i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [sum_empty, sum_empty]; exact serial.flat
  | insert a s hs ih => rw [sum_insert hs,sum_insert hs]; exact serial.plus (h a (by simp)) (ih fun i hi => h i (by simp [hi]))
lemma Jaunt.summations (s : Finset γ) (K : γ→CircM c α β) {F : γ →Momentum→CompM α β} {p : Site c} (h : ∀ i∈s,Jaunt (K i) (F i) p) : Jaunt (∑ i ∈ s,K i) (∑ i∈s,F i) p := by
  classical
  induction s using Finset.induction with
  | empty => rw [sum_empty,sum_empty]; exact Jaunt.zero p
  | insert a s ha ih => rw [sum_insert ha,sum_insert ha]; exact Jaunt.plus (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

abbrev VRange (G : Gauge) (i : ℕ) (L : Side) := Co L (Loc G i)

def areaRef (G : Gauge) (L : Side) (p : Momentum) := -(furnish L (pageD G 0) p)
def stairRow (G : Gauge) (L : Side) (v : Axis) := furnish L (fun _ => dasher G v)
def roomStart (G : Gauge) (L : Side) := ∑ i : Axis,fun p : Momentum => (stairRow G L i (-p))ᵀ

def stableF (G : Gauge) (ι : Type) (L : Side) := Film.cardF (ι:=ι) (areaRef G L)
def leapF (G : Gauge) (ι : Type) (L : Side) := Film.cardF (ι:=ι) (roomStart G L-areaRef G L)
def sectorMail (P : Patch) (E : Eye ι (Acts G P)) := (stableF G ι P.L).plus ((Dapper E).pay (leapF G ι P.L))

lemma areaNice (G : Gauge) (L : Side) : Poster σ (areaRef G L) := by
  have h : Poster σ (fun p => -(1:ℂ) • furnish L (pageD G 0) p) := ((page_linen _).furnish_ok).plus_nec _
  simp only [neg_smul,one_smul] at h; exact h
lemma rowNice (v : Axis) : Poster σ (stairRow G L v) := (Poster.web (dasher G v)).furnish_ok
lemma startNice : Poster σ (roomStart G L) := Poster.tops _ _ fun i _ => (rowNice i).reverse


section actual
variable (G) (S : StepData c f)
lemma zero_neat : Jaunt (approached (repackM (unitSplit G S 1) (unitSplit G S 0) (mail (1:Config G f)))) (areaRef G S.patch.L) 0 := by
  let X : Lines G f 1 ≃ Co c (Co S.patch.L (Loc G 1)) := unitSplit G S 1
  let Y : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  let Q := patron G (d 0 f)
  change Jaunt (approached (repackM X Y _)) _ _
  rw [show mail (1:Config G f)= -Q from mailed_zero,show repackM X Y (-Q)= -repackM X Y Q from rfl,prom_negation]
  exact (staff (S:=S) 0 (G:=G)).backside
lemma seatOpen (i : Axis) : Jaunt (approached (repackM (unitSplit G S 0) (unitSplit G S 1) (stagehand i G f))) (stairRow G S.patch.L i) 0 := by
  change Jaunt ((approached (stagehand i G f)).submatrix (splitCo S.ratio (Loc G 0)).symm (splitCo S.ratio (Loc G 1)).symm) (furnish S.ratio.count (fun _ => dasher G i)) 0
  exact Jaunt.press S.ratio (dash_far (G:=G) (n:=f) i) (σ:=1) (Poster.web _) zero_lt_one
lemma initiate : Jaunt (approached (repackM (unitSplit G S 1) (unitSplit G S 0) (restaged G f))) (roomStart G S.patch.L) 0 := by
  let A := unitSplit G S 0; let B := unitSplit G S 1
  let T := fun i => approached (repackM A B (stagehand i G f))
  have ht i : Jaunt ((T i)ᵀ) (fun p => (stairRow G S.patch.L i (-p))ᵀ) 0 := (seatOpen G S i).takes
  have hh := Jaunt.summations univ _ (fun i _ => ht i)
  have he : approached (repackM (unitSplit G S 1) (unitSplit G S 0) (restaged G f))= ∑ i : Axis,(T i)ᵀ := by ext i j; simp [approached,repackM,T,A,B,restaged, Matrix.sum_apply]
  rw [he]; exact hh
lemma jumpZero : Ticket (leapF G ι S.patch.L) (fun _ : Corn (Co c ι) => repackM (unitSplit G S 1) (unitSplit G S 0) (shiftLaunch G f)) := by
  classical
  apply Ticket.current _ _
  have he := (initiate G S).plus (zero_neat G S).backside
  let X : Lines G f 1 ≃ Co c (Co S.patch.L (Loc G 1)) := unitSplit G S 1
  let Y : Lines G f 0 ≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  change Jaunt (approached (repackM X Y _)) _ _
  let M := restaged G f; let N := mail (1:Config G f)
  rw [show shiftLaunch G f=M+ -N from sub_eq_add_neg .., show repackM X Y (M+ -N)=repackM X Y M+ -repackM X Y N from rfl,prom_addition,prom_negation,sub_eq_add_neg]; exact he
variable {G}
theorem mail_for (Z : Corn (Co c ι)→L[ℝ] Bang G c f) {D : Eye ι (Acts G S.patch)} (h : Turns D (billZ S Z)) (t : S.Choices) (r : Bool) :
    Ticket (sectorMail S.patch D) (fun x => repackM (unitSplit G S 1) (unitSplit G S 0) (mail (headOn S t r (Z x)).1)) := by
  classical
  let K : Eye ι (Acts G S.patch) := D; let U x := (headOn S t r (Z x)).1
  apply Ticket.foreign (Ticket.plus (Ticket.current (ι:=ι) (m:=c) (areaRef G S.patch.L) _ (zero_neat G S)) (Ticket.pay (bending_ticket S t r Z h) (jumpZero G S)))
  refine Eventually.of_forall (fun x => ?_); simp only [Pi.add_apply]
  change _= repackM (unitSplit G S 1) (unitSplit G S 0) (mail (U x)); conv_rhs => rw [vivid (U x),show repackM _ _ (_ + _) = repackM (unitSplit G S 1) (unitSplit G S 0) (mail (1:Config G f))+ repackM (unitSplit G S 1) (unitSplit G S 0) (motley (U x)*shiftLaunch G f) from rfl,repack_multiply _ (unitSplit G S 1)];
  rfl
end actual
end YM.Stationary
end

/-!
# Mail obtains character tariffs. `direct` costs all in strip BEFORE L.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι] {G : Gauge} {c f L : Side} {P : Patch} {C D σ : ℝ} {p q : Momentum}
section reweight
-- costs change ONLY width≤1, µ^power, no product artifacts.
lemma advance {X : Slab α} {Y T : Slab β} {A : Film ι α β} (hp : Charges X Y A σ C) (ht : ∀ p∈strip σ,serial Y T p p 1 D) : Charges X T A σ (C*D) := by
  refine ⟨hp.covered,fun h => ?_,fun i p q h => ?_,fun i j p q r h => ?_⟩
  · simpa using (hp.base h).bond (ht _ h)
  · simpa using (hp.detail i h).bond (ht _ h.basic)
  simpa using (hp.stamp i j h).bond (ht _ h.oneWay.basic)
lemma revertX {X T : Slab α} {Y : Slab β} {A : Film ι α β} (hp : Charges X Y A σ C) (ht : ∀ p∈strip σ,serial T X p p 1 D) : Charges T Y A σ (D*C) := by
  refine ⟨hp.covered,fun h => ?_,fun i p q h => ?_,fun i j p q r h => ?_⟩
  · simpa using (ht _ h).bond (hp.base h)
  · simpa using (ht _ h.added).bond (hp.detail i h)
  simpa using (ht _ h.total).bond (hp.stamp i j h)
lemma leftward (h : σ ≤ 1) (p : Momentum) (he : p∈strip σ) : serial (Slab.basic (Co L α)) (altarTile L α) p p 1 (Real.exp 4*(inch L)⁻¹) := by
    simpa only [one_mul] using cruise (L:=L) (α:=α) (σ:=1) p (fun i=> (he i).trans_le h)
lemma westward (h : σ ≤ 1) (p : Momentum) (he : p∈strip σ) : serial (altarTile L α).dual (Slab.basic (Co L α)) p p 1 (Real.exp 4*(inch L)⁻¹) := by
  simpa only [neg_neg,transpose_one,slide_basic] using (leftward (α:=α) (L:=L) h _ (negResident he)).slide
end reweight
section ahead

def stageTariff (G : Gauge) (i : Axis) : ℝ := Real.exp 4 * vflux (dasher G i) * Real.exp 4
def runTariff (G : Gauge) : ℝ := (∑ i,stageTariff G i) + pageOrd G 0
def paceTariff (G : Gauge) (j : ℕ) (C : ℝ) : ℝ := pageSmooth G 0 + 4*feeHead (dapperPrice G (muralRoom j*C))*runTariff G * Real.exp 4

lemma stableT1 (L : Side) : Charges (Slab.basic _) (altarTile L _) (stableF G ι L) 1 (pageSmooth G 0) := by
  have he p (hv : p∈strip (1:ℝ)) : serial (Slab.basic _) (altarTile L _) p p (areaRef G L p) (pageSmooth G 0) := (pageTroop L p 0 hv).neg
  exact Charges.current (areaNice _ _) ((he (0:Momentum) (Work.F07.realStrip _ zero_lt_one (by simp))).fence) he
lemma stableT2 (L : Side) : Charges (altarTile L _|>.dual) (Slab.basic _) (stableF G ι L) 1 (pageSmooth G 0) := by
  have he p (hv : p∈strip (1:ℝ)) : serial (altarTile L _|>.dual) (Slab.basic _) p p (areaRef G L p) (pageSmooth G 0) := (pageFrame L p 0 hv).neg
  exact Charges.current (areaNice _ _) ((he (0:Momentum) (Work.F07.realStrip _ zero_lt_one (by simp))).fence) he
lemma leapTariff (L : Side) : Charges (Slab.basic _) (Slab.basic _) (leapF G ι L) 1 (runTariff G) := by
  have hh (i : Axis) p (hp : p∈strip (1:ℝ)) : serial (Slab.basic _) (Slab.basic _) p p (stairRow G L i p) (stageTariff G i) := plankPrice _ hp (flux_nonneg (dasher G i)) (fun j => le_rfl)
  have hx p (hp : p∈strip (1:ℝ)) : serial (Slab.basic _) (Slab.basic _) p p (leapF G ι L|>.tab p) (runTariff G) := by
    simp only [leapF,Film.cardF,Pi.sub_apply]; refine serial.sub ?_ (serial.neg (pageBase L p _ hp))
    unfold roomStart; rw [Finset.sum_apply]; apply serial.tops; intro i _; simpa only [slide_basic,neg_neg] using (hh i (-p) (negResident hp)).slide
  exact Charges.current (Poster.shares startNice (areaNice ..)) ((hx (0:Momentum) (Work.F07.realStrip _ zero_lt_one (by simp))).fence) hx
lemma paceTariff_pays {D : Eye ι (Acts G P)} (he : Spotlight P D σ C) (hp : 0<σ) :
    Charges (Slab.basic _) (altarTile P.L _) (sectorMail P D) σ (paceTariff G P.J C) ∧
    Charges (altarTile P.L _|>.dual) (Slab.basic _) (sectorMail P D) σ (paceTariff G P.J C) := by
  have hx := (stableT1 (G:=G) (ι:=ι) P.L).mono he.width le_rfl
  have hq := (stableT2 (G:=G) (ι:=ι) P.L).mono he.width le_rfl
  have hh := (Dapper.trails he).pay ((leapTariff (G:=G) (ι:=ι) P.L).mono he.width le_rfl) hp
  unfold sectorMail paceTariff; constructor
  · apply Charges.plus hx
    convert advance hh (leftward (L:=P.L) he.width) using 1; field_simp [(inch_pos P.L).ne']
  apply Charges.plus hq
  convert revertX hh (westward (L:=P.L) he.width) using 1; field_simp [(inch_pos P.L).ne']
end ahead
end YM.Stationary
end
