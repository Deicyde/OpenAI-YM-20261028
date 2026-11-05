import YM.Next.STATIONARY.Films.Routing


set_option autoImplicit false
/-!
# Φ, vertex generic conversions for cinema. Works with external pencils
sharing inserted indices.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {ι γ : Type} [Fintype ι] [DecidableEq ι] [Fintype γ] [DecidableEq γ] {G : Gauge} {P : Patch} {c f n : Side} {p : Momentum} {σ C : ℝ}
variable (S : StepData c f)

section staging
variable (L : Corn (Co c ι)→L[ℝ] Bang G c f)
def billZ := (pavilionB G S).toContinuousLinearMap ∘L L
def plusPunch (x : Bang G c f) (v : Vault G c f) := x+(0,v,0)
def payPunch (x : Bang G c f) (v : Link G c) := x+(0,0,v)
lemma rehearsing (x : Bang G c f) (i) : rehearsal S i (pavilionB G S x) = pianist S i x := by
  simp [rehearsal]
lemma propRehearsal (i) (v : Vault G c f) (x) : rehearsal S i (billZ S L x+orbitR S true (directX G S v)) = pianist S i (plusPunch (L x) v) := by
  rw [← rehearsing]; congr 1; unfold plusPunch; rw [map_add]; congr 1
  change pavilionB G S (0, (directX G S).symm (directX G S v),0)=_
  rw [(directX G S).symm_apply_apply]
lemma propPay (i) (v : Link G c) (x) : rehearsal S i (billZ S L x+orbitV S v)=pianist S i (payPunch (L x) v) := by
  rw [← rehearsing]; congr 1; unfold payPunch; rw [map_add]; rfl
lemma punch_live : Tendsto (fun v : Corn (Co c ι)×Vault G c f => plusPunch (L v.1) v.2) (𝓝 0) (𝓝 0) := by
  let F := fun v : Corn (Co c ι)×Vault G c f => plusPunch (L v.1) v.2
  have he : F 0=0 := by simp [F,plusPunch]
  rw [show (fun v : Corn (Co c ι)×Vault G c f => _)=F from rfl,show 𝓝 (0:Bang G c f)= _ from congr_arg (𝓝 ·) he.symm]; exact (show Continuous F by unfold F plusPunch; fun_prop).continuousAt
lemma punch_cost : Tendsto (fun v : Corn (Co c ι)×Link G c => payPunch (L v.1) v.2) (𝓝 0) (𝓝 0) := by
  let F := fun v : Corn (Co c ι)×Link G c => payPunch (L v.1) v.2
  have he : F 0=0 := by simp [F,payPunch]
  rw [show (fun v : Corn (Co c ι)×Link G c => _)=F from rfl, show 𝓝 (0:Bang G c f)= _ from congr_arg (𝓝 ·) he.symm]; exact (show Continuous F by unfold F payPunch; fun_prop).continuousAt

-- From ∀ templates as row real functions on joint, using partial chart.

theorem carbon {D : Eye ι (Acts G S.patch)} (d : Turns D (billZ S L)) (F : γ → BassInput G S.patch →ℝ) (h : ∀ i, ContDiffAt ℝ ω (F i) 0) (Q : Corn (Co c ι)→ Vault G c f→Corn (Co c γ))
    (hp : ∀ i : Co c γ,∀ᶠ x in 𝓝 0,∀ᶠ y in 𝓝 0, Q x y i=F i.2 (pianist S i.1 (plusPunch (L x) y))) : Ticket (recitalX (mentor F D (fun _ => visibly S.patch true)))
      (fun x => repackM (Equiv.refl _) (clothe G S) (billsM (helmets G c f) (pocket (Co c γ)) (fderiv ℝ (Q x) 0))) := by
  classical
  let M := fun (x : Corn (Co c ι)) y => billZ S L x+orbitR S true (directX G S y)
  refine mentoring S (billZ S L) (orbitR S true) d (orbit_path S true) F h ?_
  have hv i : (rehearsal S i) (billZ S L 0)=0 := by rw [map_zero,map_zero]
  have hP j : ∀ᶠ x in 𝓝 0,∀ i : γ,ContDiffAt ℝ ω (F i) (rehearsal S j (billZ S L x)) := eventually_all.mpr fun i =>
      (show Tendsto (fun x => rehearsal S j (billZ S L x)) (𝓝 0) (𝓝 0) from hv j ▸ ((rehearsal _ _).cont.comp (billZ S L).cont).continuousAt.tendsto).eventually ((h i).eventually (by simp))
  intro i; filter_upwards [eventually_all.mpr hp,eventually_all.mpr hP] with x hx hz y
  obtain ⟨w,rfl⟩ := (directX G S).surjective y
  let T j (a : WarpV G S) := F ((j : Co c γ).2) (rehearsal S j.1 (billZ S L x+ orbitR S true a))
  let U z := orbitR (G:=G) S true z
  let K := directX G S
  have ht j : ContDiffAt ℝ ω (T j) 0 := by
    refine (ContDiffAt.comp _ ?_ <| (rehearsal S j.1).contDiff.contDiffAt.comp _ (f:=fun z=> billZ S L x + U z) (contDiffAt_const.add ((orbitR (G:=G) S true).contDiff.contDiffAt)))
    rw [map_zero, add_zero]; exact hz j.1 j.2
  have hy j : (fun y => Q x y j) =ᶠ[𝓝 0] ((T j) ∘ K) := (hx j).mono fun v hv => by
    dsimp only; rw [hv]; exact congr_arg _ (propRehearsal S L _ v x).symm
  have he : ContDiffAt ℝ ω (Q x) 0 := contDiffAt_pi.mpr fun j => (((show ContDiffAt ℝ ω (T j) (K 0) from map_zero K ▸ ht j)).comp _ K.contDiff.contDiffAt).congr_of_eventuallyEq (hy j)
  have hh := (hy i).fderiv_eq (𝕜:=ℝ)
  let A := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Co c γ => ℝ) i
  have hc := A.hasFDerivAt.comp (f:=Q x) 0 ((he.differentiableAt (by simp)).hasFDerivAt)
  rw [show fderiv ℝ (fun y => Q x y i) 0= _ from hc.fderiv,fderiv_comp _ (by rw [map_zero]; exact (ht _).differentiableAt (by simp)) K.differentiableAt,map_zero,K.fderiv] at hh
  have hh' := DFunLike.congr_fun hh w
  nth_rewrite 1 [direct_pay]; rw [repack_act,bill_at,cash_pocket]; exact hh'

end staging
end YM.Stationary
end

/-! # Rectangular readings. Includes quake X for dual L. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {ι γ : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {c f n : Side} {p : Momentum} {σ C : ℝ}
-- profile at fine site within one tile.

def hatch (P : Patch) (i : Site P.L) : P.Points := ⟨lift i,by
    have he := ((roulette P).symm i).property
    change lift i∈box (P.L.val/2) at he
    obtain ⟨ha,hv⟩ := box_test.mp he
    apply box_test.mpr
    have ht : (P.L.val/2)≤P.radius := (Nat.div_le_self ..).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact ⟨fun i => (neg_le_neg (by exact_mod_cast ht)).trans (ha i),fun i => (hv i).trans (by exact_mod_cast ht)⟩⟩

def chartersR (r : Bool) (P : Patch) (G : Gauge) (i : Loc G 1) (x : BassInput G P) := wristBox r x (axisEquiv.symm i.1) i.2
def leafletR (r : Bool) (P : Patch) (G : Gauge) (i : Co P.L (Loc G 0)) (x : BassInput G P) := rocketBox r x (hatch P i.1) i.2.2

def CharterR (r : Bool) (D : Eye ι (Acts G P)) := recitalX (mentor (chartersR r P G) D (fun _ => visibly P true))
def Chromatic (r : Bool) (D : Eye ι (Acts G P)) := recitalX (mentor (leafletR r P G) D (fun _ => visibly P true))
lemma CharterR.green (r : Bool) {D : Eye ι (Acts G P)} (h : Fresh D σ) : Play (CharterR r D) σ := cosmic_mentor h (Fresh.placed _) _
lemma Chromatic.green (r : Bool) {D : Eye ι (Acts G P)} (h : Fresh D σ) : Play (Chromatic r D) σ := cosmic_mentor h (Fresh.placed _) _
lemma color_beak (k : G.ColorIndex) : ∃ T : G.Color→L[ℝ] ℝ, (∀ x,T x=x k) ∧ ‖T‖ ≤ 1 := by
  let T : G.Color →L[ℝ] ℝ := (LinearMap.toContinuousLinearMap (LinearMap.comp (LinearMap.proj k) ((WithLp.linearEquiv 2 ℝ _).toLinearMap)))
  refine ⟨T,fun _ => rfl,ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_⟩
  rw [one_mul]; exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) (by rw [EuclideanSpace.norm_sq_eq]; exact single_le_sum (s:=univ) (f:=fun i => ‖x i‖^2) (fun _ _ => by positivity) (mem_univ k))

variable (S : StepData c f)
section fittings
variable (t : S.Choices)
lemma head_punch (r) (x : Bang G c f) (v) : headOn S t r (plusPunch x v)=headOn S t r x := by simp [headOn,plusPunch]
lemma head_pay (r) (x : Bang G c f) (v) : headOn S t r (payPunch x v)=headOn S t r x := by simp [headOn,payPunch]

variable (r : Bool) (h : S.patch.Branches S.kernel G)
include h
lemma ethic_receipts (i : Co c (Co S.patch.L (Loc G 0))) :
    ∀ᶠ x : Bang G c f in 𝓝 0,
      rocket S t (buffOn S t G r) (headOn S t r x) x.2.1 ((unitSplit G S 0).symm i)=leafletR r S.patch G i.2 (pianist S i.1 x) := by
  let T : Co f (Loc G 0) ≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  change ∀ᶠ x : Bang G c f in 𝓝 0, rocket S t _ _ x.2.1 (T.symm i)=_
  obtain ⟨⟨a,s,b⟩,rfl⟩ := T.surjective i
  have he : T (a,s,b)=(S.ratio.parent a,(S.ratio.residue a,s,b)) := split_co ..
  rw [T.symm_apply_apply, he]
  rw [vac_only s]; exact ethic S t h a b r
lemma crown_receipts (i : Lines G c 1) : ∀ᶠ x : Bang G c f in 𝓝 0,
    worn S t (buffOn S t G r) (headOn S t r x) x.2.1 i=chartersR r S.patch G i.2 (pianist S i.1 x) := by
  rcases i with ⟨i,a,b⟩; obtain ⟨k,rfl⟩ := axisEquiv.surjective a
  simp only [chartersR, axisEquiv.symm_apply_apply]; exact edict_pay S t h i k b r

variable (L : Corn (Co c ι)→L[ℝ] Bang G c f) {D : Eye ι (Acts G S.patch)}
    (hxL : ∀ i,(L i).2.1=0) (d : Turns D (billZ S L))
include hxL d

lemma issued_one : Ticket (CharterR r D) (fun x => repackM (Equiv.refl _) (clothe _ S) (quota S t (buffOn S t G r) (headOn S t r (L x)))) := by
  classical
  let C := buffOn S t G r
  let Q x y := worn S t C (headOn S t r (L x)) y
  refine carbon S L d (chartersR r S.patch G) ?_ Q ?_
  · intro i; obtain ⟨T,ht,hT⟩ := color_beak i.2; unfold chartersR; simp_rw [← ht]; exact T.contDiff.contDiffAt.comp (f:=fun x=> wristBox r x (axisEquiv.symm i.1)) _ (wrist_this h r _)
  intro i; refine ((punch_live L).eventually (crown_receipts S t r h i)).curry_nhds.mono (fun x hx => hx.mono (fun y hy => ?_));
  dsimp only at hy; rw [head_punch,show (plusPunch (L x) y).2.1=y by simp [plusPunch,hxL]] at hy; exact hy

lemma estate : Ticket (Chromatic r D)
      (fun x => repackM (unitSplit G S 0) (clothe G S) (indexX S t (buffOn S t G r) (headOn S t r (L x)))) := by
  classical
  let K := unitSplit G S 0
  let C := buffOn S t G r
  let M x y := rocket S t C (headOn S t r (L x)) y
  let W : BaseSites G f≃L[ℝ] Corn (Co c (Co S.patch.L (Loc G 0))) := LinearEquiv.toContinuousLinearEquiv (LinearEquiv.funCongrLeft ℝ ℝ K.symm)
  let Q x := W ∘ M x
  let P x := billsM (helmets G c f) (pocket _) (fderiv ℝ (Q x) 0)
  have he x : repackM K (clothe G S) (indexX S t C (headOn S t r (L x)))= repackM (Equiv.refl _) (clothe G S) (P x) := by
    unfold indexX P Q; rw [W.comp_fderiv]; ext i j
    unfold repackM; simp only [Matrix.submatrix_apply, bill_def, cash_pocket]; rfl
  refine Eq.mp (congr_arg (fun f : OperatorF ι c _ _ => Ticket (Chromatic r D) f) (funext he).symm) (?_)
  refine carbon S L d (leafletR r S.patch G) ?_ Q ?_
  · intro i; obtain ⟨T,ht,hT⟩ := color_beak i.2.2; unfold leafletR; simp_rw [← ht]; exact T.contDiff.contDiffAt.comp (f:=fun x => rocketBox r x (hatch _ i.1)) _ (rocketThis h r _)
  intro i; refine ((punch_live L).eventually (ethic_receipts S t r h i)).curry_nhds.mono (fun x hx => hx.mono (fun y hy => ?_));
  dsimp only at hy; rw [head_punch,show (plusPunch (L x) y).2.1=y by simp [plusPunch,hxL]] at hy; exact hy
end fittings
end YM.Stationary
end

/-!
# Funding both scalar and smear output. Same graph and registrations on mesh.
Smear is special application under correlated `Bang.2.2`; permitted arbitrary
activation. All from stationary native frame germ.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι] {c f : Side} (S : StepData c f) {G : Gauge} {P : Patch} {K : KernelChoices}

lemma Ticket.foreign {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {K : Film ι α β} {M N : OperatorF ι c α β} (h : Ticket K M) (hp : M =ᶠ[𝓝 0] N) : Ticket K N := by
  refine ⟨fun i j => (h.finance i j).congr_of_eventuallyEq (hp.symm.mono fun k he => congr_fun (congr_fun he i) j), ?_,fun i p q he => ?_,fun i j p q r s he hh => ?_⟩
  · rw [cardM,← hp.eq_of_nhds]; exact h.tab
  · unfold seat; rw [← art_neighbor hp]; exact h.spot _ _ _ he
  unfold cart; rw [← art_neighbor hp]; exact h.arch _ _ _ _ _ _ he hh
section gifts
variable (r : Bool) (k : ℝ)

def paperFace (x : BassInput G P) := ∑ i,presentsBox r k x i
def badgeFace (x : BassInput G P) := ∑ i,inuresBox r k x i
-- output-coarse Y field in TRUE materialization (not external false).
def smitten (x : BassInput G P) := ∑ i : Loc G 1, (x (.inr (.inr (true,i)))) * chartersR r P G i x
variable (D : Eye ι (Acts G P))
def BoomF := recitalX (sailor (paperFace (G:=G) r k) D (fun _ => visibly P true))
def CoastF := recitalX (sailor (badgeFace (G:=G) r k) D (fun _ => velvetX P))
def SmearF := recitalX (sailor (smitten (G:=G) r) D (fun _ => visibly P true))
lemma BoomF.green {σ} (h : Fresh D σ) : Play (BoomF r k D) σ := cosmic_sail h (Fresh.placed _) _
lemma CoastF.green {σ} (h : Fresh D σ) : Play (CoastF r k D) σ := cosmic_sail h (Fresh.placed _) _
lemma SmearF.green {σ} (h : Fresh D σ) : Play (SmearF r D) σ := cosmic_sail h (Fresh.placed _) _
end gifts

section activity
variable (L : Corn (Co c ι)→L[ℝ] Bang G c f) {D : Eye ι (Acts G S.patch)}
lemma caloric (F : BassInput G S.patch→ℝ) (h : ContDiffAt ℝ ω F 0) (d : Turns D (billZ S L)) (V : Corn (Co c ι) → Vault G c f → ℝ) (hp : ∀ᶠ x in 𝓝 0,∀ᶠ y in 𝓝 0,V x y=∑ i,F (pianist S i (plusPunch (L x) y))) :
    Ticket (recitalX (sailor F D (fun _ => visibly S.patch true)))
      (fun x => repackM (clothe G S) (clothe G S) (damage (helmets _ _ _) (V x) 0)) := by
  classical
  refine mariner S (billZ S L) (orbitR S true) d (orbit_path S true) F h ?_
  let M (x : Corn (Co c ι)) z := ∑ i, F (rehearsal S i (billZ S L x+orbitR S true z))
  let X := directX G S
  have hu i : Tendsto (fun x => rehearsal S i (billZ S L x)) (𝓝 0) (𝓝 0) := (show rehearsal S i (billZ S L 0)=0 by simp) ▸ ((rehearsal S i).cont.comp (billZ S L).cont).continuousAt.tendsto
  have hh i : ∀ᶠ x in 𝓝 0,ContDiffAt ℝ ω F (rehearsal S i (billZ S L x)) := (hu i).eventually (h.eventually (by simp))
  filter_upwards [eventually_all.mpr hh,hp] with x hx hp y z
  obtain ⟨a,rfl⟩ := X.surjective y; obtain ⟨b,rfl⟩ := X.surjective z
  have hc : V x =ᶠ[𝓝 0] (M x ∘ X) := hp.mono (fun i hi => by rw [hi]; unfold M X; simp only [Function.comp_apply,propRehearsal])
  have hy : ContDiffAt ℝ ω (M x) 0 := by
    apply ContDiffAt.sum
    intro i _
    let T : WarpV G S → Corn (Co c (Acts G S.patch)) := fun z => billZ S L x+orbitR S true z
    have he : ContDiffAt ℝ ω F (rehearsal S i (T 0)) := by unfold T; rw [map_zero, add_zero]; exact hx i
    exact he.comp (f:=fun z => rehearsal S i (T z)) _ ((rehearsal S i).contDiff.contDiffAt.comp (f:=T) _ (contDiffAt_const.add (orbitR S true).contDiff.contDiffAt))
  have he : iteratedFDeriv ℝ 2 (M x∘X) 0 ![a,b]=iteratedFDeriv ℝ 2 (M x) 0 ![X a,X b] := by
    have ht := wired X.toContinuousLinearMap (f:=M x) (x:=0) (by rw [map_zero]; exact hy.analyticAt) 2 ![a,b]
    rw [map_zero,show X.toContinuousLinearMap ∘ ![a,b]=![X a,X b] by ext1 i; fin_cases i <;> rfl] at ht; exact ht
  change dotProduct (X a) (repackM _ _ _*ᵥ X b)= iteratedFDeriv ℝ 2 (M x) 0 ![X a,X b]
  rw [← he,← (hc.iteratedFDeriv ℝ 2).eq_of_nhds]; unfold X; rw [direct_pay,direct_pay,repack_act, ← repack_dot,detracts]

variable (h : S.patch.Branches S.kernel G) (t : S.Choices) (r : Bool)

def honorsBox (x : Corn (Co c ι)) := damage (helmets G c f)
    (fun y => tickets S (input G c (L x).1.1) (ribbon S t (atire (buffOn S t G r) (headOn S t r (L x)) y))) 0
def motions (x : Corn (Co c ι)) := damageC S t (buffOn S t G r) (input G c (L x).1.1) (headOn S t r (L x))

variable (hq : ∀ i,(L i).2.1=0) (d : Turns D (billZ S L))
include h hq d
lemma honorsGift : Ticket (BoomF r S.kernel.penalty D) (fun x => repackM (clothe G S) (clothe G S) (honorsBox S L t r x)) := by
  classical
  refine caloric S L (paperFace (G:=G) r S.kernel.penalty) (ContDiffAt.sum (fun i _ => presents_this h r _ i)) d _ ?_
  refine ((punch_live L).eventually (boom_line S t h r)).curry_nhds.mono (fun i hi => hi.mono (fun y hy => ?_)); dsimp only at hy; rw [head_punch,show (plusPunch (L i) y).1=(L i).1 by simp [plusPunch],show (plusPunch (L i) y).2.1=y by simp [plusPunch,hq]] at hy; exact hy
lemma coastGift (hy : ∀ i,(L i).2.2=0) : Ticket (CoastF r S.kernel.penalty D) (motions S L t r) := by
  let E i x := ∑ v,badgeFace r S.kernel.penalty (rehearsal S v (billZ S L i+orbitV S x))
  refine mariner S (billZ S L) (orbitV S) d (velvet_path S) _ (ContDiffAt.sum fun i _ => inuresThis h r _ i) ?_
  filter_upwards [((punch_cost L).eventually (inured_line S t h r)).curry_nhds] with i hi x y
  let T := inure S (input G c (L i).1.1) (ribbon S t (dress (buffOn S t G r) (headOn S t r (L i))))
  have he : T =ᶠ[𝓝 0] (E i) := hi.mono (fun j hv => by
    unfold T E
    simp_rw [propPay]; rw [head_pay,show (payPunch (L i) j).1=(L i).1 by simp [payPunch],show (payPunch (L i) j).2.2=j by simp [payPunch,hy]] at hv; exact hv)
  change dotProduct x ((damage _ T 0)*ᵥ y)=iteratedFDeriv ℝ 2 (E i) 0 _
  have ht := detracts (pocket (Lines G c 1)) T 0 x y
  rw [cash_pocket,cash_pocket,(he.iteratedFDeriv ℝ 2).eq_of_nhds] at ht; exact ht

-- `K` rotates with L.external; need hShell? no
omit d in
lemma ornamental : ∀ i : Lines G c 1, ∀ᶠ x in 𝓝 0,∀ᶠ y in 𝓝 0,
    worn S t (buffOn S t G r) (headOn S t r (L x)) y i=chartersR r S.patch G i.2 (pianist S i.1 (plusPunch (L x) y)) := by
  intro i; refine (((punch_live L).eventually (crown_receipts S t r h i)).curry_nhds).mono fun x hx => ?_
  exact hx.mono (fun y hy => by dsimp only at hy; rw [head_punch, show (plusPunch (L x) y).2.1=y by simp [plusPunch,hq]] at hy; exact hy)
lemma sun_shipped : Ticket (SmearF r D) (fun x => repackM (clothe G S) (clothe G S) (smear S t (buffOn S t G r) (headOn S t r (L x)) (L x).2.2)) := by
  classical
  let M x := worn S t (buffOn S t G r) (headOn S t r (L x))
  let y x := (L x).2.2
  let F x z := dotProduct (y x) (M x z)
  have ht : ∀ᶠ x in 𝓝 0, ∀ᶠ z in 𝓝 0,F x z=∑ i,smitten r (pianist S i (plusPunch (L x) z)) := by
    filter_upwards [eventually_all.mpr (ornamental S L h t r hq)] with x hx
    filter_upwards [eventually_all.mpr hx] with z hz
    unfold F dotProduct; rw [Fintype.sum_prod_type]; refine sum_congr rfl fun i _ => ?_; refine sum_congr rfl fun j _ => ?_
    rw [show M x z (i,j)= _ from hz (i,j)]; congr 1
    change y x _=y x _+0; rw [add_zero]
  have hh i : ContDiffAt ℝ ω (chartersR r S.patch G i) 0 := by obtain ⟨P,hP,hg⟩ := color_beak i.2; unfold chartersR; simp_rw [← hP]; exact P.contDiff.contDiffAt.comp (f:=fun x=> wristBox r x (axisEquiv.symm i.1)) _ (wrist_this h r _)
  have hb := caloric S L (smitten r) (show ContDiffAt ℝ ω _ 0 from ContDiffAt.sum fun i _ => (contDiffAt_apply _ _ _ _).mul (hh i)) d F ht
  have hY : ∀ᶠ x in 𝓝 0,ContDiffAt ℝ ω (M x) 0 := by
    -- want derive from ornamental, snapshot L. ∀ columns FSC
    have hl i : Tendsto (fun x => pianist S i (L x)) (𝓝 0) (𝓝 0) := (show pianist S i (L 0)=0 by simp) ▸ ((pianist S i).cont.comp L.cont).continuousAt.tendsto
    have hK (j : Lines G c 1) := (hl j.1).eventually ((hh j.2).eventually (by simp))
    filter_upwards [eventually_all.mpr hK,eventually_all.mpr (ornamental S L h t r hq)] with x hx hu
    refine contDiffAt_pi.mpr fun i => (ContDiffAt.comp (f:=fun z => pianist S i.1 (plusPunch (L x) z)) 0 (g:=chartersR r S.patch G i.2) ?_ (?_ : ContDiffAt ℝ ω _ _)).congr_of_eventuallyEq (hu i)
    · change ContDiffAt ℝ ω _ (pianist S i.1 (plusPunch (L x) 0)); rw [show plusPunch (L x) 0=L x from add_zero _]; exact hx i
    exact (pianist _ _).contDiff.contDiffAt.comp _ (f:=fun y => plusPunch (L x) y) (by unfold plusPunch; fun_prop)
  have he : (fun x => repackM (clothe G S) (clothe G S) (damage (helmets G c f) (F x) 0)) =ᶠ[𝓝 0]
      fun x => repackM (clothe G S) (clothe G S) (smear S t (buffOn S t G r) (headOn S t r (L x)) (L x).2.2) := by
    filter_upwards [hY] with x hx; apply congr_arg
    ext i j; unfold damage smear lapel; rw [LinearMap.toMatrix₂_apply,Work.F05.bend_apply,Matrix.of_apply]
    let T : Link G c →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (dotProductBilin ℝ ℝ (y x)); exact DFunLike.congr_fun (T.iteratedFDeriv_comp_left hx le_top) _
  -- patch exactly at germs.
  exact hb.foreign he
end activity
end YM.Stationary
end

/-!
# Serial unit tests in cell budget. Receipt shape and Cast/ext tracked.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β δ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
variable {G : Gauge} {P : Patch} {K : KernelChoices} {A : Audience α} {C D σ : ℝ} {m n : ℕ} {p q : Momentum}

section normal
lemma entity {U : Phase α} (X : Slab α) (q : Momentum) (h : U≠0) : 0 < X.rate q U :=
    slug_pos (fun hp => h (by rw [← X.rebate q U,hp,mulVec_zero]))
lemma entity_scaling (X : Slab α) (p) (u : Phase α) (c : ℂ) : X.rate p (c • u)= ‖c‖*X.rate p u := by unfold Slab.rate; rw [Matrix.mulVec_smul,slug_scale]
lemma normed_unit_test (X : Slab α) (U : Phase α) (q) (h : U ≠ 0) : X.rate q ( ((X.rate q U:ℂ))⁻¹ • U) = 1 := by
  rw [entity_scaling,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (entity X q h),inv_mul_cancel₀ (entity X q h|>.ne')]
lemma stands_rate (K : CompM α β) {X : Slab α} {Y : Slab β} (hc : 0≤C) (h : ∀ u, Y.rate p u ≤ 1 → X.rate q (K*ᵥ u)≤C) : serial X Y q p K C := by
  refine Slab.serial_of hc fun i => ?_
  by_cases hz : i=0
  · rw [hz, mulVec_zero]; simp [Slab.rate,slug_zero, hc]
  have hu := h _ (normed_unit_test Y i p hz).le
  have hy := entity Y p hz
  rw [Matrix.mulVec_smul, entity_scaling, norm_inv,Complex.norm_real,Real.norm_eq_abs, abs_of_pos hy, inv_mul_eq_div] at hu; exact (div_le_iff₀ hy).mp hu
lemma stands_echo (K : CompM α β) {X : Slab α} {Y : Slab β} (hc : 0≤C) (h : ∀ u v, X.rate (-q) u ≤ 1 → Y.rate p v ≤ 1 → ‖dotProduct u (K*ᵥ v)‖≤C) : serial X.dual Y q p K C := by
  refine Slab.cost_of hc fun i y => ?_
  by_cases hz : i=0
  · rw [hz, zero_dotProduct]; simp [Slab.rate,slug_zero, hc]
  by_cases hv : y=0
  · rw [hv,mulVec_zero,dotProduct_zero]; simp [Slab.rate,slug_zero,hc]
  have he := h _ _ (normed_unit_test X i (-q) hz).le (normed_unit_test Y y p hv).le
  have hi := entity X (-q) hz
  have hy := entity Y p hv
  rw [Matrix.mulVec_smul, smul_dotProduct,dotProduct_smul,norm_smul,norm_inv,norm_smul,norm_inv,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hy,abs_of_pos hi,inv_mul_eq_div,inv_mul_eq_div,div_le_iff₀ hi,div_le_iff₀ hy] at he; exact he

lemma serial_caps {K : Leagues ι α β} {X : Slab α} {Y : Slab β} (d : Play (recitalX K) σ) (h : ∀ n≤2,∀ i : Fin n→ι,∀ v : Fin n→Momentum,(∀ i, v i∈ strip σ) → ∀ p∈strip σ, sunshift v p∈strip σ → serial X Y (sunshift v p) p (K n v i p) C) : Charges X Y (recitalX K) σ C := by
  refine ⟨d,fun hz => ?_,fun i p q hp => ?_,fun i j p q r hp => ?_⟩
  · simpa [recitalX,sunshift] using h 0 (by decide) ![] ![] (by simp) _ hz (by simpa [sunshift] using hz)
  · simpa [recitalX,sunshift] using h 1 (by decide) ![i] ![p] (fun i=> by fin_cases i; exact hp.side) q hp.basic (by simpa [sunshift] using hp.added)
  simpa [recitalX, sunshift, Fin.sum_univ_two] using h 2 le_rfl ![i,j] ![p,q] (fun i => by fin_cases i; exact hp.oneWay.side; exact hp.second.side) r hp.oneWay.basic (by simpa [sunshift,Fin.sum_univ_two] using hp.total)

def feeHead (f : ℕ→ℝ) : ℝ := ∑ i ∈ range 3, |f i|
lemma fee_ge (f : ℕ→ℝ) {k} (h : k≤2) : f k ≤ feeHead f := (le_abs_self _).trans (single_le_sum (s:=range 3) (fun i _ => abs_nonneg (f i)) (mem_range.mpr (by omega)))
end normal

-- common allowance for every ext. K≥ e^4. Need momentum `skin` either only charges of exists σ independent. C(H) pre-L
structure Spotlight (P : Patch) (E : Eye ι (Acts G P)) (σ C : ℝ) : Prop where
  width : σ≤1
  fresh : Fresh E σ
  price : Real.exp 4 ≤ C
  paint i : ∀ p∈strip σ, Veil (P:=P) C (E p (Pi.single i 1)) 0

namespace Spotlight
variable {E : Eye ι (Acts G P)} (h : Spotlight P E σ C)
include h
lemma brighten (hp : p∈strip σ) : p∈strip (1:ℝ) := fun i => (hp i).trans_le h.width
lemma full_price : 0 ≤ C := (Real.exp_pos _).le.trans h.price
lemma payload : 1 ≤ C := (Real.one_le_exp (by norm_num)).trans h.price
lemma bright_lens (v : Fin n→ Momentum) (q : Fin n→ ι) (he : ∀ i,v i∈strip σ) :
    ∀ i, Shiny (StaffP G P (muralRoom P.J*C)) (lens (inviton E q v) v i) 0 := fun i => shiny_steps _ (h.paint (q i) _ (he i)) (h.brighten (he i))
end Spotlight
lemma spotlight_cape {Φ : Bridge G P} (h : Ties Φ σ C) (hx : C≥ Real.exp 4) (hp : Poster σ Φ) (ht : σ≤1) : Spotlight P (arriving Φ) σ C := ⟨ht,Fresh.enter hp,hx, fun p _ hr => bends_affect ((Real.one_le_exp (by norm_num)).trans hx) h hr p⟩
end YM.Stationary
end
