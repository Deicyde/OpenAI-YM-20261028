import YM.Next.STATIONARY.Films.RankColor

set_option autoImplicit false
/-!
# Shear legasion. Represents adjoint inverse read in centered display but
ROOTED at the observer. No norm charged outside qualitative FFT. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {K : KernelChoices} {σ A C D : ℝ} {c f L : Side}
-- template for tailor:
-- fine bank x.1 increment; exact via Lie chart. χ=log(crews).

def crewFrame (v : Bool) (x : BassInput G P) := pianoC v x none * (entryCap P (pianoU v x))⁻¹
def crewVerse (p : ParcelG G P.L) (x : BassInput G P) : ℝ := match p with
    | .inl (a,u) => x (.inl (true,harpoon P a,u))
    | .inr t => plogC G (crewFrame true x * (crewFrame false x)⁻¹) t.2

def CutFilm (E : Eye ι (Acts G P)) := recitalX (mentor (crewVerse (P:=P) (G:=G)) E (fun _ => visibly P true))
lemma CutFilm.green {E : Eye ι (Acts G P)} (h : Fresh E σ) : Play (CutFilm E) σ := cosmic_mentor h (Fresh.placed _) _
lemma headcrew_zero (h : P.Branches K G) (v : Bool) : crewFrame v (0:BassInput G P)=1 := by simp [crewFrame,entryCap,pianoC_origin,piano_origin,entry_zero h,focus_zero]
lemma knownCrew (h : P.Branches K G) (i) : ContDiffAt ℝ ω (crewVerse (P:=P) (G:=G) i) 0 := by
  have hx (v : Bool) : Army (fun x : BassInput G P => (fun _ : Unit => crewFrame v x)) 0 := by
    intro i
    have ht : Army (fun x => fun _ : Unit => entryCap P (pianoU v (x:BassInput G P))) 0 := fun i => cap_fold h (piano_army v) (piano_origin v)
    have hv := (ring3 (A:=balcony Unit) (G:=G) (P:=P) (n:=0) v (le_refl 0) none).listen ()
    exact hv.mul (ht.inv i)
  rcases i with ⟨a,b⟩|i
  · exact contDiffAt_apply ..
  obtain ⟨P',hP,hP'⟩ := color_beak i.2
  let T := fun x : BassInput G P => G.mat (crewFrame true x * (crewFrame false x)⁻¹)
  have he : T 0=1 := by simp [T, headcrew_zero h]
  change ContDiffAt ℝ ω (fun x => G.plog (T x) i.2) _
  simp_rw [← hP]; exact P'.contDiff.contDiffAt.comp (f:=fun x => G.plog (T x)) _ ((show ContDiffAt ℝ ω G.plog (T 0) from he ▸ G.plog_diff).comp (f:=T) _ (((hx true).mul (hx false).inv) ()))

section periods
variable (S : StepData c f) (t : S.Choices)
    (X : Corn (Co c ι) →L[ℝ] Bang G c f)
variable (h : S.patch.Branches S.kernel G)
include h
lemma crewing (v : Bool) (i : Site c) : ∀ᶠ x : Bang G c f in 𝓝 0, (finalBang S t false v x).2 i = crewFrame v (pianist S i x) := by
  filter_upwards [piano_pact S h v i, centered_wire S t h (initial_nice (G:=G) (c:=c) (f:=f) v).1 (by rw [initial_zero]; rfl) i 0] with x hx hu
  unfold crewFrame; simp only [piano_tops,Option.map,Option.getD]
  change (initialBang v x).2 i * (bears S t _ i)⁻¹=_; rw [hu.1]; unfold entryCap entryHat; rw [hx.1]
lemma crews (i : Site c) (j : ParcelG G S.patch.L) : ∀ᶠ x : Bang G c f in 𝓝 0,
    directX G S (tailor (fedora S t) (headOn S t false x) x.2.1) (i,j)=crewVerse j (pianist S i x) := by
  let W x := tailor (fedora S t) (headOn S t false x) ((x:Bang G c f).2.1)
  have he x : (W x).1=content (input G f x.2.1.1) := by
    change content ((input _ _ x.2.1.1 * _) * _⁻¹) = _; simp [dress]
  have hp x : gaugeColor (W x).2 i= plogC G (((finalBang S t false true x).2 i)*((finalBang S t false false x).2 i)⁻¹) := by
    unfold W tailor retract; rw [stayBack,pulledOn, show buffOn S t G false=fedora S t from rfl]; simp [frameLog]
  have hx : ∀ᶠ x : Bang G c f in 𝓝 0,(W x).1=x.2.1.1 := by
    let Z := fun x : Bang G c f => x.2.1.1
    have h : Tendsto Z _ (𝓝 0) := (show Continuous Z by unfold Z; fun_prop).tendsto 0
    filter_upwards [h.eventually (input_encodes (G:=G) (m:=f))] with x hx; rw [he]; exact hx
  filter_upwards [hx,crewing S t h true i,crewing S t h false i] with x he hv ht
  change directX G S (W x) (i,j)= _
  cases j with
  | inl a =>
    rcases a with ⟨u,b⟩; let T := directX G S
    have hv : ((wrap c (rent S.patch.L (lift u)))+i)=i := by rw [rent_lift,map_zero,zero_add]
    have hh := direct_low S (W x) (lift u) i b; rw [hv,wrap_lift, he] at hh; exact hh
  | inr a =>
    rcases a with ⟨u,b⟩; rw [direct_high, crewVerse, ← ht, ← hv,vac_only u]; exact congr_arg (fun z : G.Color=> z b) (hp x)

lemma Cut_ticket {E : Eye ι (Acts G S.patch)} (hp : Turns E (billZ S X)) (hW : ∀ i,(X i).2.1=0) : Ticket (CutFilm E) (fun x => repackM (clothe G S) (clothe G S) (shear (fedora S t) (headOn S t false (X x)))) := by
  classical
  let T := directX G S
  let C := clothe G S
  let M x := tailor (fedora S t) (headOn S t false (X x))
  let Y x := T∘ M x
  have he : Ticket (CutFilm E) (fun x => repackM (Equiv.refl _) C (billsM (helmets G c f) (pocket _) (fderiv ℝ (Y x) 0))) := by
    refine carbon S X hp _ (knownCrew h) Y (fun i => ?_)
    refine ((punch_live X).eventually (crews S t h i.1 i.2)).curry_nhds.mono (fun x hx => hx.mono fun v hv => ?_)
    change directX _ _ _ _ = _ at hv
    dsimp only at hv
    rw [head_punch,show (plusPunch (X x) v).2.1=v by simp [plusPunch,hW]] at hv; exact hv
  apply he.foreign; refine Eventually.of_forall fun i => ?_; unfold Y; simp only [T.comp_fderiv]
  ext p q; change billsM _ _ _ p (C.symm q)=billsM _ _ _ (C.symm p) (C.symm q); rw [bill_def,bill_def,cash_pocket]; rfl
end periods
end YM.Stationary
end

/-!
# Two-channel mixed calorimeter. Tag eyes as actual α (coarse thermal)
or Y-test from separate coarse link space.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {α β γ ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {G : Gauge} {P : Patch} {K : KernelChoices} {σ A C D : ℝ} {c f L : Side}
section mix
abbrev Tweaks (ι κ : Type) := ι⊕κ

-- spatial seats as pair projection.
def tunerL {R : Type} [CommSemiring R] : (Co c (Tweaks ι κ) → R) →ₗ[R] (Co c ι→R) := LinearMap.pi fun i=> LinearMap.proj (i.1,Sum.inl (β:=κ) i.2)
def tunerR {R : Type} [CommSemiring R] : (Co c (Tweaks ι κ)→ R)→ₗ[R] (Co c κ→ R) := LinearMap.pi fun i=> LinearMap.proj (i.1,Sum.inr (α:=ι) i.2)

def cleanL (m : Side) (ι κ : Type) [Fintype ι] [Fintype κ] : Corn (Co m (ι⊕κ)) →L[ℝ] Corn (Co m ι) := LinearMap.toContinuousLinearMap tunerL
def cleanR (m : Side) (ι κ : Type) [Fintype ι] [Fintype κ] : Corn (Co m (ι⊕κ))→L[ℝ] Corn (Co m κ) := LinearMap.toContinuousLinearMap tunerR

def Cleaned (F : Film ι α β) (κ : Type) : Film (Tweaks ι κ) α β where
  tab := F.tab
  spot i := match i with | .inl v=> F.spot v | .inr _=> 0
  arch i j := match i,j with | .inl v,.inl k => F.arch v k | _,_=>0
lemma Creative (F : Film ι α β) (T : OperatorF ι c α β) (h : Ticket F T) : Ticket (Cleaned F κ) (T ∘ cleanL c ι κ) := by
  let L := cleanL c ι κ
  let Y : Phase (Co c (ι⊕κ)) →ₗ[ℂ] Phase (Co c ι) := tunerL
  have hu (i : Co c α) j : ContDiffAt ℝ ω (fun x => T x i j) (L 0) := map_zero L ▸ h.finance _ _
  have hM n (v : Fin n→ Phase (Co c (ι⊕κ))) : art (T ∘ L) n v=art T n (Y ∘ v) := by
    ext i j; unfold art; simp only [Matrix.of_apply]; rw [show (fun a => (T ∘ L) a i j)= (fun a=> T a i j) ∘ L from rfl, evaluated Y (L:=L) (fun v=>rfl) (h.finance i j|>.analyticAt) n]; rfl
  have hx i (p : Site c) : Y (relay p (.inl i))=relay p i := by
    ext1 t; simp [Y, tunerL, relay,tune, Pi.single_apply]
  have hz i (p : Site c) : Y (relay p (.inr i))=0 := by
    ext1 t; simp [Y, tunerL,relay,tune,Pi.single_apply]
  have he (M : OperatorF ι c α β) n (p : Fin n→ Phase (Co c ι)) (i : Fin n) (ht : p i=0) : art M n p=0 := by ext a b; exact MultilinearMap.map_coord_zero _ i ht
  refine ⟨fun i j => (hu _ _).comp _ L.contDiff.contDiffAt,?_,fun i p q hv => ?_,fun i j p q t r he' hy => ?_⟩
  · rw [cardM,Function.comp_apply, map_zero]; exact h.tab
  · unfold seat; rw [show art _ _ _= _ from hM 1 _]; rcases i with i |i
    · rw [show Y ∘ (![relay p _] : Fin 1 → _)=![relay p i] by funext k; fin_cases k; exact hx ..]; exact h.spot i p q hv
    rw [he _ _ _ 0 (hz i p)]; exact Jaunt.zero _
  unfold cart; rw [show art _ _ _= _ from hM 2 _]; rcases i with i | i
  · rcases j with j|j
    · rw [show Y ∘ (![relay p _,relay q _]:Fin 2 → _)=![relay p i,relay q j] by funext k; fin_cases k; exact hx i p; exact hx j q]; exact h.arch i j p q t r he' hy
    rw [he _ _ _ 1 (hz j q)]; exact Jaunt.zero _
  rcases j with j|j <;> (rw [he _ _ _ 0 (hz i p)]; exact Jaunt.zero _)
lemma FreshCleanup (F : Film ι α β) (hp : Play F σ) : Play (Cleaned F κ) σ := by
  refine ⟨hp.tab,(fun i=>?_),(fun i j=> ?_)⟩
  · rcases i with i | i; · exact hp.spot i
    exact (Play.current (ι:=ι⊕κ) (Poster.web (σ:=σ) (0:CompM α β))).spot (Sum.inr i)
  rcases i with i|i
  · rcases j with j|j; · exact hp.arch i j
    exact (Play.current (ι:=ι⊕κ) (Poster.web (σ:=σ) (0:CompM α β))).arch (.inl i) (Sum.inr j)
  rcases j with j|j; exact (Play.current (ι:=ι⊕κ) (Poster.web (σ:=σ) (0:CompM α β))).arch (Sum.inr i) (Sum.inl j); exact (Play.current (ι:=ι⊕κ) (Poster.web (σ:=σ) (0:CompM α β))).arch (.inr i) (.inr j)

def Fillet (F : Eye ι α) (K : Eye κ α) : Eye (ι⊕κ) α := fun p =>
    ((F p).comp (shardX ι κ ℂ).mulVecLin) + ((K p).comp (shardY ι κ ℂ).mulVecLin)
lemma FreshFillet (F : Eye ι α) (K : Eye κ α) (he : Fresh F σ) (hp : Fresh K σ) : Fresh (Fillet F K) σ := by
  refine ⟨fun h w => ?_,fun h u => ?_⟩
  · simp only [Fillet,he.shifts h w,hp.shifts h w]
  exact (he.sense h _).add (hp.sense h _)
lemma FilletTurns (F : Eye ι α) (K : Eye κ α) {M N} (h : Turns F M) (hp : Turns K N) : Turns (c:=c) (Fillet F K) (M ∘L (cleanL c ι κ) + N ∘L (cleanR c ι κ)) := by
  obtain ⟨Y,H,H'⟩ := h.basis; obtain ⟨X,T,T'⟩ := hp.basis
  refine ⟨(Y.comp tunerL) + (X.comp tunerR),fun u => ?_, fun p q h v=> ?_⟩
  · rw [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.comp_apply, show tunerL (axes u)=axes (cleanL c ι κ u) from rfl, show tunerR (axes u)= axes (cleanR c ι κ u) from rfl,H,T]; ext1 i; simp [axes]
  rw [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.comp_apply, show tunerL (tune p v)=tune p (v∘ Sum.inl) from rfl,show tunerR (tune p v)= tune p (v ∘ Sum.inr) from rfl,H' _ _ h, T' _ _ h]
  unfold Fillet; simp only [LinearMap.add_apply,LinearMap.comp_apply,Matrix.mulVecLin_apply, sliceX,sliceY]; ext1 i; simp [tune,mul_add]
end mix
end YM.Stationary
end

/-!
# Compute doubly tagged determinant insertions. No rooted casting costs
supplied. S algebra used off-shell only for Nb; at same orbit.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {K : KernelChoices} {σ A C D η : ℝ} {c f L : Side}

section mixes
abbrev ScoreBoard (G : Gauge) := Loc G 1⊕Loc G 1
abbrev DuoBoard (G : Gauge) (c : Side) := Corn (Co c (ScoreBoard G))
-- instances DecidableEq
instance duo_score (G : Gauge) : DecidableEq (ScoreBoard G) := fun a b => instDecidableEqSum a b
instance duet_card (G : Gauge) (c : Side) : DecidableEq (Co c (ScoreBoard G)) := fun a b => instDecidableEqProd a b
-- modified Jacob test.
variable (X : Matrix (Body 1 f) (Body 1 c) ℝ)
def partL (G : Gauge) (c : Side) : DuoBoard G c→L[ℝ] Link G c := cleanL c (Loc G 1) (Loc G 1)
def partR (G : Gauge) (c : Side) : DuoBoard G c→L[ℝ] Link G c := cleanR c (Loc G 1) (Loc G 1)
def partsHand : DuoBoard G c→L[ℝ] Bang G c f := (saluteLe X ∘L partL G c).prod ((0: DuoBoard G c→L[ℝ] Vault G c f).prod (partR G c))

variable (E : Eye (Loc G 1) (Acts G P))
def seamUp (k : ℝ) (T : Spark (Loc G 1) G P) := let R := (legionF E false T k).back; ((CutFilm E).pay R).pay (CutFilm E|>.rear)
def seamLeft (k : ℝ) (T : Spark (Loc G 1) G P) := Cleaned (seamUp E k T) (Loc G 1)
def commandY := SmearF true (Fillet E (fun _=> velvetX P))
def carrierY (k : ℝ) (T : Spark (Loc G 1) G P) := (seamLeft E k T).pay (commandY E)
lemma carrier_live {U : Spark (Loc G 1) G P} {k : ℝ} (h : Fresh E σ) (ht : Play (legionF E false U k) σ) (hv : Freezer (slabW G P.L|>.dual) (slabW G P.L) (legionF E false U k).tab σ C) : Play (carrierY E k U) σ := by
  have hx := ht.back hv.period; have hc := CutFilm.green h
  have hy := FreshCleanup (seamUp E k U) (κ:=Loc G 1) (((hc.pay hx).pay hc.rear))
  have hm : Play (commandY E) σ := SmearF.green true (Fillet E (fun _ => velvetX P)) (FreshFillet _ _ h (Fresh.placed _))
  exact hy.pay hm
end mixes

lemma backRepacked {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {K : Film ι b b} {U : Corn (Co c ι) → Funds a} (e : a≃Co c b) (h : Ticket K (fun x => repackM e e (U x))) (hp : IsUnit (U 0).det) : Ticket K.back (fun x => repackM e e (U x)⁻¹) := by
  have he : IsUnit (repackM e e (U 0)).det := by rw [repack_det]; exact hp
  apply (h.back he).foreign
  filter_upwards [(h.finance.det_val.continuousAt).eventually_ne he.ne_zero] with x hx
  change (repackM e e (U x)).det ≠ 0 at hx; rw [repack_det] at hx; exact (repack_scale_inv _ _ hx.isUnit).symm
section period
variable {r : Clip} {R : PathData G} {S : StepData c f} (t : S.Choices)
    {F : Forest S.ratio} {ρ} (h : Critical F r R ρ)
    (X : Matrix (Body 1 f) (Body 1 c) ℝ) (hp : R.Bounds r σ A D) (hy : S.patch.Branches S.kernel G) (hv : PriceGap F r R η) (hz : 0<η) {M : Eye (Loc G 1) (Acts G S.patch)}
    (ht : Turns M (atlasQ S X))
    {N : Spark (Loc G 1) G S.patch} (hn : Ticket N (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (flare r R (input G f (uniformM (G:=G) X x)))))
include h hp hy hv hz ht hn
lemma seams : Ticket (seamUp M S.kernel.penalty N) (fun x => repackM (clothe G S) (clothe G S) (legion S t r R (inch S.patch.L) 1 (input _ _ x) (chevron S t X x))⁻¹) := by
  -- precedence: reindex on inverse
  classical
  let T := clothe G S
  let μ := inch S.patch.L
  let C := fedora S t (G:=G)
  let K x := Stationary.extend (endorse (G:=G) X x)
  let U x := shear C (K x)
  let V x := input G c x
  let Y := chevron (G:=G) S t X
  let L x := legion S t r R μ C (V x) (K x)
  let Q x := legion S t r R μ 1 (V x) (Y x)
  have hi : Ticket (legionF M false N S.kernel.penalty) (fun x=> repackM T T (L x)) := legislature S t false (cardHand (G:=G) X) ht hy (fun _=>rfl) (fun _=>rfl) hn
  have hM : Ticket (CutFilm M) (fun x => repackM T T (U x)) := Cut_ticket S t (cardHand X) hy ht (fun _=>rfl)
  have hK : Thaw K 0 := Thaw.through (v:=fun x => endorse (G:=G) X x) (endorse X).contDiff.contDiffAt
  have hP : K 0=1 := by simp [K]
  have hx : V 0=1 := input_zero ..
  have hL : IsUnit (L 0).det := by unfold L; rw [hP,hx,legion_origin hy hp t _ (fedora_style hy t)]; exact (moment_track h hy hp t (inch_pos _) hv hz).1.ne'.isUnit
  have hT := backRepacked (U:=L) (K:= legionF M false N S.kernel.penalty) T hi hL
  have HH := (hM.pay hT).pay hM.rear
  apply HH.foreign
  have hv' : Thaw Y 0 := chevron_lit S t X hy
  have hx : (Y 0).1=1 := by rw [show Y 0=1 from chevron_zero S t X hy]; rfl
  have hK : ∀ᶠ z in 𝓝 0,Apparel C (K z) := atire_out (fedora_style hy t) hK (by rw [hP]; rfl)
  filter_upwards [awake t hp hv' hx hy root_customs,hK,explosive S t hy root_customs hv' hx] with x hx hK hG
  have he : L x=(U x)ᵀ* Q x * U x := fields S t r R μ C _ _ hK hG hx.wist
  have hu : IsUnit (U x).det := by rw [show (U x).det=1 from shear_det C (K x) hK]; exact isUnit_one
  have hx : U x * (L x)⁻¹ * (U x)ᵀ=(Q x)⁻¹ := by
    rw [he,Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc (U x) (U x)⁻¹, Matrix.mul_nonsing_inv _ hu, one_mul,Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (by rw [det_transpose]; exact hu),mul_one]
  refine Eq.trans ?_ (congr_arg (repackM T T) hx); rw [repack_multiply T T, repack_multiply T T T (U x)]
  rfl

omit hn h hp hv hz in
lemma smearedX : Ticket (commandY M) (fun x => repackM (clothe G S) (clothe G S) (smear S t 1 (chevron S t X (partL G c x)) (partR G c x))) := by
  classical
  let L := partsHand (G:=G) X
  have he : billZ S L= atlasQ S X ∘L (partL G c)+ orbitV S ∘L partR G c := by
    apply ContinuousLinearMap.ext; intro x
    let y := partL G c x; let z := partR G c x
    have hp : L x=(saluteLe X y,0,z) := rfl
    rw [show billZ S L x=pavilionB G S (L x) from rfl,hp,show (saluteLe X y,(0:Vault G c f),z)=((saluteLe X y,(0:(Vault G c f) × _)):Bang G c f) + (0,0,z) by simp, map_add]; rfl
  have ht : Turns (Fillet M (fun _ => velvetX S.patch)) (billZ S L) := by rw [he]; exact FilletTurns _ _ ht (velvet_path S)
  exact sun_shipped S L hy t true (fun _=>rfl) ht
-- Beware precedence; wish root inverse before reindex. explicitly as W of repacks; don't need invert outside unit matrices.
def rondo (r : Clip) (R : PathData G) (x : DuoBoard G c) :=
    let a := partL G c x; let u := chevron S t X a
    repackM (clothe G S) (clothe G S) ((legion S t r R (inch S.patch.L) 1 (input G c a) u)⁻¹) *
      repackM (clothe G S) (clothe G S) (smear S t 1 u (partR G c x))
lemma carry_root : Ticket (carrierY M S.kernel.penalty N) (rondo t X r R) :=
    (Creative _ _ (seams t h X hp hy hv hz ht hn)).pay (smearedX t X hy ht)
end period
end YM.Stationary
end

/-!
# Mixed Y momentum Ward. Complete–uncontact logarithm along merit,
 trace identity with observation channel.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] {G : Gauge} {c f : Side} {S : StepData c f}

lemma repack_trace (e : ι≃β) (u : Funds ι) : (repackM e e u).trace=u.trace := by unfold trace; exact Equiv.sum_comp e.symm (fun i => u i i)

-- observer embeddings

def boardR {κ : Type} [Field κ] : (Lines G c 1 → κ) →ₗ[κ] (Co c (ScoreBoard G) → κ) := {
  toFun u i := Sum.elim (fun _=>0) (fun v=> u (i.1,v)) i.2
  map_add' a b := funext fun i => by rcases i with ⟨i,j|j⟩ <;> simp
  map_smul' a b := funext fun i => by rcases i with ⟨i,j|j⟩ <;> simp }
def boardL {κ : Type} [Field κ] : (Lines G c 1 → κ) →ₗ[κ] (Co c (ScoreBoard G) → κ) := {
  toFun u i := Sum.elim (fun v => u (i.1,v)) (fun _=>0) i.2
  map_add' a b := funext fun i => by rcases i with ⟨i,j|j⟩ <;> simp
  map_smul' a b := funext fun i => by rcases i with ⟨i,j|j⟩ <;> simp }
abbrev boardA (G : Gauge) (c : Side) : Link G c →L[ℝ] DuoBoard G c := LinearMap.toContinuousLinearMap boardL
abbrev boardB (G : Gauge) (c : Side) : Link G c →L[ℝ] DuoBoard G c := LinearMap.toContinuousLinearMap boardR
@[simp] lemma face_A (x : Link G c) : partL G c (boardA G c x)=x := rfl
@[simp] lemma face_B (x : Link G c) : partR G c (boardB G c x)=x := rfl
@[simp] lemma pose_A (x : Link G c) : partL G c (boardB G c x)=0 := rfl
@[simp] lemma pose_B (x : Link G c) : partR G c (boardA G c x)=0 := rfl

section viewpoints
variable (t : S.Choices) (r : Clip) (R : PathData G) (X : Matrix (Body 1 f) (Body 1 c) ℝ)
def clears (b : DuoBoard G c) := (rondo t X r R b).trace
def clouds (b : DuoBoard G c) := ((rondo t X r R b)*(rondo t X r R b)).trace
lemma clears_out (x) : clears t r R X x=dotProduct (partR G c x) (drossY X r R t (inch S.patch.L) (partL G c x)) := by
  classical
  let K:= clothe G S
  unfold clears rondo drossY; dsimp only; rw [← repack_multiply K, repack_trace, earn_ad]
lemma board_bounce (h : S.patch.Branches S.kernel G) (x) :
    rondo t X r R (boardB G c x) = repackM (clothe G S) (clothe G S) ((legion S t r R (inch S.patch.L) 1 1 1)⁻¹*smear S t 1 1 x) := by
  classical
  unfold rondo; simp only [face_B,pose_A, input_zero]; rw [chevron_zero S t X h]; exact (repack_multiply (clothe G S) (clothe G S) ..).symm
lemma volley_pay (h : S.patch.Branches S.kernel G) (hx : AnalyticAt ℝ (clouds t r R X) 0) (u v : Link G c) :
    iteratedFDeriv ℝ 2 (clouds t r R X) 0 ![boardB G c u, boardB G c v] =
      let M := (legion S t r R (inch S.patch.L) 1 1 1)⁻¹
      2*((M*smear S t 1 1 u*M)*smear S t 1 1 v).trace := by
  dsimp only; let M := (legion S t r R (inch S.patch.L) 1 1 1)⁻¹; change _=2*((M*smear S t 1 1 u*M)*smear S t 1 1 v).trace
  let J := t
  let N := Bodies G c f
  classical
  let L := fun x : Link G c => M*smear S t 1 1 x
  let f := fun x => ((L x)*(L x)).trace
  have he x : f x=(clouds t r R X) (boardB G c x) := by rw [clouds,board_bounce t r R X h,← repack_multiply (clothe G S),repack_trace]
  have ha : Memo L 0 := by
    apply Memo.cross (Memo.raw M _)
    intro i j; unfold smear; simp only [Matrix.of_apply,dotProduct]; refine ContDiffAt.sum fun k _ => ?_; exact (contDiffAt_apply ℝ ℝ k _).mul contDiffAt_const
  have hu (a b) : ContDiffAt ℝ ω (fun x => L x a b) 0 := ha ..
  have hK a b : ∃ T : Link G c→L[ℝ] ℝ, (fun x => L x a b)=T := by
    classical
    let T : Link G c→ₗ[ℝ] ℝ := ∑ i,∑ j : Lines G c 1, (M a i * lapel S t 1 1 i b j) • LinearMap.proj j
    refine ⟨T.toContinuousLinearMap,funext fun x => ?_⟩
    change L x a b= T x; simp only [L,T,Matrix.mul_apply,smear,Matrix.of_apply,dotProduct,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply, Finset.mul_sum,smul_eq_mul]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hz : iteratedFDeriv ℝ 2 f 0 = iteratedFDeriv ℝ 2 (clouds t r R X ∘ boardB G c) 0 := by rw [show f=_ from funext he]; rfl
  have hm := wired (boardB G c) (by rw [map_zero]; exact hx) 2 ![u,v]; rw [map_zero,show (boardB G c) ∘ ![u,v]= ![boardB G c u,boardB G c v] by ext1 i; fin_cases i <;> rfl] at hm
  rw [← hm,← hz]
  have hv (i j : N) : iteratedFDeriv ℝ 2 (fun x => L x i j * L x j i) 0 ![u,v]=L u i j*L v j i+L v i j * L u j i := by
    obtain ⟨T,hT⟩ := hK i j; obtain ⟨F,hF⟩ := hK j i; simp_rw [show ∀ x, L x i j= T x from congr_fun hT, show ∀ x, L x j i= F x from congr_fun hF]
    let t (x : Link G c) : Unit→ℝ := fun _=>T x; let l (x) : Unit→ℝ := fun _=>F x
    have ht : ContDiffAt ℝ ω t 0 := contDiffAt_pi.mpr fun _=> T.contDiff.contDiffAt; have hl : ContDiffAt ℝ ω l 0 := contDiffAt_pi.mpr fun _=> F.contDiff.contDiffAt
    have hx : t 0=0 := funext fun _=>map_zero _; have hs : l 0=0 := funext fun _=>map_zero _
    have he (v z) : fderiv ℝ t 0 v z=T v := by
      let Y := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Unit=>ℝ) z
      have ht : fderiv ℝ T 0=T := T.fderiv
      rw [← ht]; exact DFunLike.congr_fun (Eq.symm (show fderiv ℝ T 0=Y ∘L fderiv ℝ t 0 from (Y.hasFDerivAt.comp _ ((show ContDiffAt ℝ ω t _ from ‹_›).differentiableAt (by simp)).hasFDerivAt).fderiv)) v
    have hk (v z) : fderiv ℝ l 0 v z=F v := by
      let Y := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Unit=>ℝ) z
      exact DFunLike.congr_fun (Eq.trans (Eq.symm (show fderiv ℝ F 0=Y ∘L fderiv ℝ l 0 from (Y.hasFDerivAt.comp _ (hl.differentiableAt (by simp)).hasFDerivAt).fderiv)) F.fderiv) v
    have hw := dot_quadr ht hl hx hs u v
    simpa only [dotProduct,Fintype.sum_unique,he,hk,t,l] using hw
  rw [show f=(fun x => ∑ i,∑ j,L x i j*L x j i) from rfl, iteratedFDeriv_fun_sum_apply (f:=fun i x=>∑ j,L x i j*L x j i) (fun i _ => ContDiffAt.sum fun j _ => ((ha ..).mul (ha ..)|>.of_le le_top)),_root_.sum_apply]
  rw [show 2*((M*smear S t 1 1 u*M)*smear S t 1 1 v).trace=(L u*L v).trace+(L v*L u).trace by rw [trace_mul_comm (L v),two_mul,Matrix.mul_assoc (M*_)]]
  unfold Matrix.trace; rw [← sum_add_distrib]; refine sum_congr rfl fun i _ => ?_; rw [iteratedFDeriv_fun_sum_apply (f:=fun j x=> L x i j*L x j i) (fun j _ => ((ha ..).mul (ha ..)|>.of_le le_top)), _root_.sum_apply, Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply,Matrix.mul_apply,← sum_add_distrib]
  exact sum_congr rfl fun j _ => hv i j
end viewpoints
end YM.Stationary
end

/-!
# α marking precision call passage REAL and link gauges for root query.
No station input jet symmetry tacit. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] {G : Gauge} {c f : Side} {S : StepData c f}
section homeland
variable (t : S.Choices) {Z : Robe G c f} {F : Forest S.ratio} {r : Clip} {R : PathData G} {ρ} {σ A D η γ : ℝ}
    (h : Critical F r R ρ) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (hp : R.Bounds r σ A D) (hy : S.patch.Branches S.kernel G) (hv : PriceGap F r R η) (hz : 0<η)
    (hk : Guessed F W ρ) (hS : G.Simple)

def narrative (W : Matrix (Body 1 f) (Body 1 c) ℝ) (F : Forest S.ratio) (ρ : Bid.Dir G c → AxisChart G F) (p : Clip) (R : PathData G) := honorarium F t (inch S.patch.L) p R ρ-upperCore S t p R ∘ saluteLe W

include h hp hy hv hz hk hS
lemma double_c (u v : Link G c) : iteratedFDeriv ℝ 2 (clears t r R W) 0 ![boardA G c u, boardB G c v] = dotProduct v (fderiv ℝ (drossY W r R t (inch S.patch.L)) 0 u) := by
  let p := partR G c; let T := partL G c
  let F := drossY W r R t (inch S.patch.L)
  have hh : ContDiffAt ℝ ω F 0 := rind_diff hy t hp _ (chevron_lit _ _ W hy) (chevron_zero S t W hy) _ (Army.powL contDiffAt_id) (input_zero ..) (unit_ud h hp t hy (inch_pos _) hv hz) (inch_pos _)
  have he : F 0=0 := by unfold F drossY; rw [input_zero,chevron_zero S t W hy, armor_zero h hp t hy (inch_pos _) hv hz hS]
  have ht : fderiv ℝ (F∘T) 0=fderiv ℝ F 0 ∘L T := by
    rw [fderiv_comp _ (by rw [map_zero]; exact hh.differentiableAt (by simp)) T.differentiableAt, map_zero,T.fderiv]
  rw [show clears t r R W=(fun x=> dotProduct (p x) ((F ∘ T) x)) from funext (fun _ => clears_out ..),
    dot_quadr (P:=p) (Q:=F ∘ T) p.contDiff.contDiffAt ((show ContDiffAt ℝ ω F (T 0) from map_zero T ▸ hh).comp _ T.contDiff.contDiffAt) (p.map_zero) (by simp [he]),p.fderiv,ht]
  unfold p T; simp only [ContinuousLinearMap.comp_apply]; change dotProduct 0 _ + dotProduct v (fderiv ℝ F 0 u)=_; rw [zero_dotProduct,zero_add]
lemma choir_ward (u : BaseSites G c) (v : Link G c) : iteratedFDeriv ℝ 2 (clears t r R W) 0 ![boardA G c (gradientA G c u),boardB G c v]=0 := by
  rw [double_c t h W hp hy hv hz hk hS, y_stems t h hp hk hy hv hz (inch_pos S.patch.L), guard_y h hp t hy (inch_pos S.patch.L) hv hz hS, dotProduct_zero]
lemma audited (B T : Bed) (he : Inputs S W (B.metric.acts f) (T.metric.acts c)) (hx : AnalyticAt ℝ (clouds t r R W) 0) (x y : Link G c) :
    iteratedFDeriv ℝ 2 (narrative t W F ρ r R) 0 ![x,y]=
      let J := -(uniformM (G:=G) (Precision.K (T.metric.acts c)))
      (1/2:ℝ)*(iteratedFDeriv ℝ 2 (clears t r R W) 0 ![boardA G c x,boardB G c (J y)] +
               iteratedFDeriv ℝ 2 (clears t r R W) 0 ![boardA G c y,boardB G c (J x)] -
               (1/2:ℝ)* iteratedFDeriv ℝ 2 (clouds t r R W) 0 ![boardB G c (J x),boardB G c (J y)]) := by
  let K := inch S.patch.L
  let J := (-(uniformM (G:=G) (Precision.K (T.metric.acts c))))
  let L := saluteLe (G:=G) W; let H := majorBoon S t r R K; let Q := coreBoon S t r R K
  let Y (x : Link G c) := grenade K (Stationary.extend (L x).2).1
  let P x := Real.log (Y x).det; let U := honorarium F t K r R ρ
  have ha : AnalyticAt ℝ P 0 := by
    have hh : Thaw (fun x => Stationary.extend (L x).2) 0 := Thaw.through L.contDiff.contDiffAt.snd
    exact ((Memo.det_val (memo_flash (inch_pos S.patch.L) hh.1).2.2).log (grenade_safe (μ:=K) _ (inch_pos _)).det_pos.ne').analyticAt
  have hb := memo_dross (p:=r) (R:=R) (μ:=K) t hy hp (by rw [legion_origin hy hp t _ (fedora_style hy t)]; exact (moment_track h hy hp t (inch_pos _) hv hz).1.ne'.isUnit) (inch_pos S.patch.L)
  have hQ : AnalyticAt ℝ (Q ∘ L) 0 := ((show ContDiffAt ℝ ω Q (L 0) from map_zero L ▸ hb.1).comp _ L.contDiff.contDiffAt).analyticAt
  have hM : AnalyticAt ℝ (H ∘ L) 0 := ((show ContDiffAt ℝ ω H (L 0) from map_zero L ▸ hb.2).comp _ L.contDiff.contDiffAt).analyticAt
  have hU : AnalyticAt ℝ U 0 := by
    obtain ⟨C,hC⟩ := LocalH.actual G
    exact (campaign h hy hp t hv hz (inch_pos S.patch.L) hC).2.1.analytic
  have hs : iteratedFDeriv ℝ 2 U 0=iteratedFDeriv ℝ 2 ((1/2:ℝ) • (H ∘ L) - P) 0 := elect h hy hp t (inch_pos S.patch.L) hS W hk hv hz
  dsimp only
  change iteratedFDeriv ℝ 2 (U-((1/2:ℝ) • (Q ∘ L)-P)) _ _= _
  have h₁ : AnalyticAt ℝ ((1/2:ℝ) • (Q ∘ L)) 0 := AnalyticAt.const_smul hQ
  have h₂ : AnalyticAt ℝ ((1/2:ℝ) • (H ∘ L)) 0 := AnalyticAt.const_smul hM
  rw [iteratedFDeriv_sub_apply hU.contDiffAt (h₁.sub ha|>.contDiffAt),hs,iteratedFDeriv_sub_apply h₁.contDiffAt ha.contDiffAt,iteratedFDeriv_sub_apply h₂.contDiffAt ha.contDiffAt]
  rw [iteratedFDeriv_const_smul_apply hQ.contDiffAt, iteratedFDeriv_const_smul_apply hM.contDiffAt,sub_sub_sub_cancel_right,_root_.sub_apply,_root_.smul_apply,_root_.smul_apply]
  rw [double_c t h W hp hy hv hz hk hS,double_c t h W hp hy hv hz hk hS,volley_pay t r R W hy hx]
  rw [show iteratedFDeriv ℝ 2 (H ∘ L) _ _=_ from lean_drift t h hp hk hy hv hz (inch_pos S.patch.L) hS _ _ he x y];
  dsimp only; simp only [Pi.neg_apply,_root_.neg_apply,smul_eq_mul,Q,K,L]; ring
end homeland
end YM.Stationary
end

/-!
# Courier in radiance. Keep Σ direction tags even when evaluated in same
ray. Beat op & powers, link Ward.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {ι β κ : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] {G : Gauge} {c f : Side} {S : StepData c f}
section linear

lemma branKit (H : Corn β → ℝ) (M : Phase ι→ₗ[ℂ] Phase β) (u : Phase β) : Leads fun v => beat H 0 2 ![M v,u] := by
  convert linear_u (beat H 0 _) ((![(0:Phase β),u]) : Fin 2→_) 0 M using 1
  ext1 i; congr 1; ext1 j; fin_cases j <;> simp
lemma branLite (H : Corn β → ℝ) (M : Phase ι→ₗ[ℂ] Phase β) (u : Phase β) : Leads fun v => beat H 0 2 ![u,M v] := by
  convert linear_u (beat H 0 _) ((![u,(0:Phase β)]) : Fin 2→_) 1 M using 1
  ext1 i; congr 1; ext1 j; fin_cases j <;> simp
lemma be_twin (H : Corn β → ℝ) (x y : Corn β) : beat H 0 2 ![axes x,axes y] = ↑(iteratedFDeriv ℝ 2 H 0 ![x,y]) := by
  rw [show (![axes x,axes y]:Fin 2 → _)=axes ∘ ![x,y] by ext1 j; fin_cases j <;> rfl,beat_real]
lemma be_factor (M : Corn κ → ℝ) (F : Corn ι→ℝ) (H Y : Corn β→ ℝ) (L K : Corn ι→L[ℝ] Corn β) (U V : Phase ι→ₗ[ℂ] Phase β)
    (hu : ∀ p,U (axes p)=axes (L p)) (hv : ∀ p,V (axes p)=axes (K p)) (hh : ∀ x y,
       iteratedFDeriv ℝ 2 F 0 ![x,y]=(1/2:ℝ)*(iteratedFDeriv ℝ 2 H 0 ![L x,K y]+iteratedFDeriv ℝ 2 H 0 ![L y,K x]-(1/2:ℝ)*iteratedFDeriv ℝ 2 Y 0 ![K x,K y])) (x y : Phase ι) :
    beat F 0 2 ![x,y] = (1/2:ℂ)*(beat H 0 2 ![U x,V y]+beat H 0 2 ![U y,V x]-(1/2:ℂ)*beat Y 0 2 ![V x,V y]) := by
  refine Leads.two (p:=fun x y => beat F 0 _ ![x,y]) (q:=fun x y => (1/2:ℂ)*(beat H 0 2 ![U x,V y]+beat H 0 2 ![U y,V x]-(1/2:ℂ)*beat Y 0 2 ![V x,V y])) (left_beat F) (right_beat F) (fun y => ?_) (fun x => ?_) ?_ x y
  · exact ((((branKit H U _).plus (branLite H V _)).sub ((branKit Y V _).cost (1/2))).cost (1/2))
  · exact ((((branLite H V _).plus (branKit H U _)).sub ((branLite Y V _).cost (1/2))).cost (1/2))
  intro a b; rw [hu,hu,hv,hv,be_twin,be_twin,be_twin,be_twin,hh a b]; push_cast; rfl
end linear
section cast
lemma boardAxes (x : Link G c) : boardL (axes x)=axes (boardA G c x) := by ext1 i; rcases i with ⟨i,j|j⟩; exact rfl; exact Complex.ofReal_zero.symm
lemma boardOr (x : Link G c) : boardR (axes x)=axes (boardB G c x) := by ext1 i; rcases i with ⟨i,j|j⟩; exact Complex.ofReal_zero.symm; rfl

def minusTax (V : Bed) : Phase (Lines G c 1)→ₗ[ℂ] Phase (Lines G c 1) := -(approached (patron G (Precision.K (V.metric.acts c)))).mulVecLin
lemma pay_tax (V : Bed) (x : Link G c) : minusTax V (axes x)=axes (-(uniformM (G:=G) (Precision.K (V.metric.acts c)) x)) := by
  simp only [minusTax, LinearMap.neg_apply,Matrix.mulVecLin_apply, prom_vec,patron_fee]; ext1 i; simp [axes]
lemma tax_birth (B : Bed) (h : B.metric.safe) (p : Site c) (q : Momentum) (hs : rolls (mon p) q) (v : Phase (Loc G 1)) : minusTax B (tune p v)=tune p (-(rug G B q*ᵥ v)) := by
  simp only [minusTax,LinearMap.neg_apply,Matrix.mulVecLin_apply,rug_plane _ B h _ _ hs,add_zero]; ext1 i; simp [tune]
end cast

section actual
variable {F : Forest S.ratio} {ρ} {r : Clip} {R : PathData G} (t : S.Choices) {σ A D η γ : ℝ}
    (h : Critical F r R ρ) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (hp : R.Bounds r σ A D) (hy : S.patch.Branches S.kernel G) (hv : PriceGap F r R η) (hz : 0<η)
    (hk : Guessed F W ρ) (hS : G.Simple)
include h hp hy hv hz hk hS
lemma audit_open (B D : Bed) (he : Inputs S W (B.metric.acts f) (D.metric.acts c)) (hx : AnalyticAt ℝ (clouds t r R W) 0) (u v : Phase (Lines G c 1)) :
    beat (narrative t W F ρ r R) 0 2 ![u,v] = (1/2:ℂ)*(beat (clears t r R W) 0 2 ![boardL u,boardR (minusTax D v)]+beat (clears t r R W) 0 2 ![boardL v,boardR (minusTax D u)]-(1/2:ℂ)*beat (clouds t r R W) 0 2 ![boardR (minusTax D u),boardR (minusTax D v)]) := by
  let L := boardA G c; let K := boardB G c ∘L (-(uniformM (G:=G) (Precision.K (D.metric.acts c))))
  let y (x) := boardR (minusTax (G:=G) (c:=c) D x)
  exact be_factor (fun _ : Corn Unit => 0) _ _ _ L K boardL (boardR.comp (minusTax D)) boardAxes (fun i => by rw [LinearMap.comp_apply,pay_tax,boardOr]; rfl) (fun i y => audited t h W hp hy hv hz hk hS B D he hx i y) u v
lemma wax_off (u : Phase (Lines G c 0)) (v : Phase (Lines G c 1)) : beat (clears t r R W) 0 2 ![boardL (approached (patron G (d 0 c))*ᵥ u),boardR v]=0 := by
  let T := clears t r R W
  -- different types. poly scalar
  let M := (approached (patron G (d 0 c))).mulVecLin
  refine Leads.buys (p:=fun v => beat T 0 2 ![boardL (M v),boardR _]) (q:=fun _ => (0:ℂ)) (branKit T (boardL.comp M) _) (fun _ _ => by simp) (fun x => ?_) u
  refine Leads.buys (p:=fun v => beat T 0 2 ![boardL (M (axes x)),boardR v]) (q:=fun _ => (0:ℂ)) (branLite T boardR _) (fun _ _ => by simp) (fun i => ?_) _
  rw [show M (axes x)=axes (gradientA G c x) by rw [first_uniform]; exact (prom_vec ..).trans (congr_arg axes (patron_fee ..)),boardAxes,boardOr,be_twin, show iteratedFDeriv ℝ 2 T 0 _=0 from choir_ward t h W hp hy hv hz hk hS _ _]; exact Complex.ofReal_zero
end actual
end YM.Stationary
end

/-!
# Root playback spectra may have *qualitative* budgets only. Longitude cancels
without any fixed-L shape costs assigned to the drift mark. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] {G : Gauge} {p q : Momentum} {σ C A τ : ℝ}
section properties
lemma skyPeriod (h : p∈strip σ) (hp : rolls p q) : q∈strip σ := by
  obtain ⟨i,rfl⟩ := hp; exact fun j => by simpa [reciprocal] using h j

def pier (σ : ℝ) := {p : Momentum | Nave p ∧ ∀ i, |(p i).im| ≤ σ}
lemma pier_closed (σ : ℝ) : IsClosed (pier σ) := by
  have he : pier σ=(⋂ i : Axis, {p : Momentum| |(p i).re|≤Real.pi}) ∩ (⋂ i : Axis, {p : Momentum| |(p i).im|≤σ}) := by ext; simp [pier,Nave]
  rw [he]; exact (isClosed_iInter (fun i : Axis => isClosed_le (show Continuous fun p : Momentum => |(p i).re| from by fun_prop) continuous_const)).inter (isClosed_iInter fun i => isClosed_le (show Continuous fun p : Momentum => |(p i).im| from by fun_prop) continuous_const)
lemma pier_compact (σ : ℝ) (h : 0 ≤ σ) : IsCompact (pier σ) := by
  apply (Metric.isCompact_iff_isClosed_bounded).2
  refine ⟨pier_closed σ,(Metric.isBounded_closedBall (x:=(0:Momentum)) (r:=Real.pi+σ)).subset ?_⟩
  rintro v ⟨hv,hx⟩; rw [Metric.mem_closedBall,dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]; intro i
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add (hv i) (hx i))
lemma calm_into {f : Momentum→ Momentum→ℂ}
    (h : Highlights σ f) (hp : 0 < τ) (he : τ<σ) : ∃ A : ℝ,Firm τ A (starTrack f) := by
  let S := Set.prod (pier τ) (pier τ)
  have hu (p : Momentum) (hp : p∈pier τ) : p∈strip σ := fun i=> (hp.2 i).trans_lt he
  have hF : ContinuousOn (fun z : Momentum×Momentum=> ‖f z.1 z.2‖) S := fun i hi=> ((h.eligible (hu _ hi.1) (hu _ hi.2)).continuousAt.norm).continuousWithinAt
  obtain ⟨A,hA⟩ := (((pier_compact τ hp.le).prod (pier_compact τ hp.le)).image_of_continuousOn hF).bddAbove
  have hy (p : Momentum) (hp : p∈strip τ) : p ∈ strip σ := fun i=> (hp i).trans he
  refine ⟨A,highlights (Highlights.mk (fun hx hr=> h.eligible (hy _ hx) (hy _ hr)) (fun h1 h2 hp hq => h.rolls h1 h2 (hy _ hp) (hy _ hq))) hp ?_⟩
  intro i hi j hj
  obtain ⟨l,hl,hl'⟩ := Nave.roll i; obtain ⟨k,hk,hk'⟩ := Nave.roll j
  have hq := skyPeriod hi hl'.symm; have hr := skyPeriod hj hk'.symm
  rw [← h.rolls hl' hk' (hy _ hq) (hy _ hr)]; exact hA ⟨(l,k),⟨⟨hl,fun j => (hq j).le⟩,⟨hk,fun j => (hr j).le⟩⟩,rfl⟩
end properties

section traces
variable {M : Film ι β β} {c : Side} {X : OperatorF ι c β β}

lemma trace_view (X : OperatorF ι c β β) (h : Memo X 0) : ContDiffAt ℝ ω (fun x=> (X x).trace) 0 := ContDiffAt.sum fun i _ => h i i
lemma cart_trace (h : Memo X 0) (u v) :
    beat (fun x=>(X x).trace) 0 2 ![u,v]=(cart X u v).trace := by
  unfold Matrix.trace
  apply Eq.trans (b:=∑ i, beat (fun z => (X z) i i) 0 2 ![u,v]) (?_)
  · rfl
  exact beat_summations univ (fun i x=>X x i i) (fun i _=> h i i) _

def hatchTrace (F : Film ι β β) (i j : ι) (p q : Momentum) := (F.arch i j (-p) p q).trace

lemma trace_spot (hs : 0<σ) (h : Play M σ) (i j : ι) : ∃ C : ℝ,Firm (σ/4) C (starTrack (hatchTrace M i j)) := by
  let F := hatchTrace M i j
  have hx := h.arch i j
  have ht : Highlights (σ/2) F := by
    refine ⟨fun he hh => ?_,fun h1 h2 he hh => congr_arg Matrix.trace (hx.shifts h1.neg h1 h2 (duo _ _ hs he hh))⟩
    exact BillD.collects (hx.go (p:=fun z : Momentum × Momentum=> -z.1) (q:=Prod.fst) (r:=Prod.snd) (duo _ _ hs he hh) (differentiableAt_fst.neg) differentiableAt_fst differentiableAt_snd)
  exact calm_into ht (by linarith) (by linarith)

lemma trace_emits (h : Ticket M X) (p : Site c) (q) (hp : rolls (mon p) q) (i j : ι) :
    beat (fun z=> (X z).trace) 0 2 ![relay (-p) i, relay p j]= (cents c:ℂ)*shop c (hatchTrace M i j q) := by
  rw [cart_trace h.finance,(h.arch i j _ _ _ _ hp.flip_sign hp).accounting,neg_add_cancel,if_pos rfl]; unfold shop
  rw [mul_inv_cancel_left₀]; rfl
  exact_mod_cast cents_pos.ne'
end traces
end YM.Stationary
end

/-!
# Period family audit to Fourier message. Amplitudes real-cost (
per cell c, counting); q continuation uses reciprocal for both sides. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] {G : Gauge} {c f : Side} {S : StepData c f} {σ A C D γ : ℝ}

section unit
lemma boardsL (p : Site c) (i : Loc G 1) : boardL (relay p i) = relay p (.inl i : ScoreBoard G) := by ext1 v; rcases v with ⟨v,k|k⟩ <;> simp [boardL,relay,tune,Pi.single_apply]
lemma boardsR (p : Site c) (i : Loc G 1) : boardR (relay p i) = relay p (.inr i : ScoreBoard G) := by ext1 v; rcases v with ⟨v,k|k⟩ <;> simp [boardR,relay,tune,Pi.single_apply]
lemma relay_value (p : Site c) (v : Phase β) : tune p v=∑ i,v i • relay p i := by ext1 i; simp [Finset.sum_apply, relay, tune, Pi.single_apply,mul_comm]
lemma relay_or (p : Site c) (v : Phase (Loc G 1)) : boardR (tune p v)=∑ i,v i • relay p (Sum.inr i:ScoreBoard G) := by rw [relay_value,map_sum]; simp_rw [map_smul,boardsR]
lemma relay_an (p : Site c) (v : Phase (Loc G 1)) : boardL (tune p v)=∑ i,v i • relay p (Sum.inl i:ScoreBoard G) := by rw [relay_value,map_sum]; simp_rw [map_smul,boardsL]
lemma directing (M : Corn β→ℝ) (p : Phase β) (v : ι→Phase β) (u : Phase ι) : beat M 0 2 ![p,∑ i,u i • v i]=∑ i,u i * beat M 0 2 ![p,v i] := by
  let L := (beat M 0 2).toLinearMap ![p,0] 1
  have he x : L x=beat M 0 2 ![p,x] := by
    change beat M 0 2 (update (![p,_]) 1 x)=_
    congr 1; ext1 i; fin_cases i <;> simp
  simp_rw [← he, map_sum,map_smul]; rfl
lemma unsung (M : Corn β→ℝ) (p : Phase β) (v : ι→Phase β) (u : Phase ι) : beat M 0 2 ![∑ i,u i • v i,p]=∑ i,u i * beat M 0 2 ![v i,p] := by
  let L := (beat M 0 2).toLinearMap ![0,p] 0
  have he x : L x=beat M 0 2 ![x,p] := by
    change beat M 0 2 (update ![0,p] 0 x)=_; congr 1; ext1 i; fin_cases i <;> simp
  simp_rw [← he,map_sum,map_smul]; rfl
end unit

lemma tune_shop (M : Award G) (h : Screened M σ C) {p : Site c} (q : Momentum) (hp : rolls (mon p) q) (i j) : shop c (M i j (mon p))=shop c (M i j q) := by
  unfold shop; congr 1; apply sum_congr rfl; intro b _
  let x := Sum.elim (mon p) (mon b)
  have he := h.earns i j
  let z := Sum.elim q (mon b)
  have hh : rolls x z := by
    obtain ⟨y,rfl⟩ := hp; refine ⟨Sum.elim y 0,?_⟩; ext1 v; cases v <;> simp [reciprocal,x,z]
  exact hh.apply he (he.in_range (by
    have hx := real_frequency p; have hb := real_frequency b
    funext v; cases v with
    | inl a => exact congr_fun hx a
    | inr a => exact congr_fun hb a))

def taxTone (G : Gauge) (D : Bed) (p : Momentum) (v : Loc G 1) : Phase (Loc G 1) := -(rug G D p *ᵥ Pi.single v 1)
section protocols
-- projections traces exact. selected Ξ mark
variable {F : Forest S.ratio} {ρ} {r : Clip} {R : PathData G} (t : S.Choices)
    (h : Critical F r R ρ) (X : Matrix (Body 1 f) (Body 1 c) ℝ) (hp : R.Bounds r σ A D) (hy : S.patch.Branches S.kernel G) (hv : PriceGap F r R γ) (hz : 0<γ) (hk : Guessed F X ρ) (hS : G.Simple) {M : Eye (Loc G 1) (Acts G S.patch)}
    (ht : Turns M (atlasQ S X))
    {N : Spark (Loc G 1) G S.patch} (hn : Ticket N (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (flare r R (input G f (uniformM (G:=G) X x)))))

include t h hp hy hv hz hk hS ht hn
lemma signing_here (B T : Bed) (he : Inputs S X (B.metric.acts f) (T.metric.acts c)) (hw : T.metric.safe)
    (p : Site c) (q : Momentum) (hs : rolls (mon p) q) (i j : Loc G 1) {η : ℝ} (hM : Screened (changeCue M S.kernel.penalty N) η C) :
    let U := carrierY M S.kernel.penalty N
    let x := taxTone G T (-q) i
    let y := taxTone G T q j
    shop c (changeCue M S.kernel.penalty N i j q)= (1/2:ℂ)*(
      ((∑ a,y a * shop c (hatchTrace U (.inl i) (.inr a) q)) + (∑ a,x a * shop c (hatchTrace U (.inl j) (.inr a) (-q)))) -
         (1/2:ℂ)* ∑ a,x a*∑ b,y b*shop c (hatchTrace (U.pay U) (.inr a) (.inr b) q)) := by
  classical
  intro U x y
  let K := rondo t X r R
  let M' := narrative t X F ρ r R; let F' := clears t r R X; let T' := clouds t r R X
  have hp' : Ticket U K := carry_root t h X hp hy hv hz ht hn
  have hd := hp'.pay hp'
  have he' : AnalyticAt ℝ T' 0 := (trace_view _ hd.finance).analyticAt
  have hb : AnalyticAt ℝ (upperCore S t r R ∘ saluteLe (G:=G) X) 0 := by
    let Q := upperCore S t r R
    let L := saluteLe (G:=G) X
    let k := inch S.patch.L
    have H : Thaw (fun x : Point G c f => Stationary.extend x.2) 0 := Thaw.through contDiffAt_snd
    have hu := (((memo_flash (inch_pos S.patch.L) H.1).2.2).det_val.log (grenade_safe _ (inch_pos _)).det_pos.ne')
    have he := memo_dross t hy hp (μ:=k) (by rw [legion_origin hy hp t _ (fedora_style hy t)]; exact (moment_track h hy hp t (inch_pos _) hv hz).1.ne'.isUnit) (inch_pos S.patch.L)
    have hn' : AnalyticAt ℝ Q 0 := (ContDiffAt.sub (ContDiffAt.mul contDiffAt_const he.1) hu).analyticAt
    exact ((show ContDiffAt ℝ ω Q (L 0) from map_zero L ▸ hn'.contDiffAt).comp _ L.contDiff.contDiffAt).analyticAt
  obtain ⟨Z,hZ⟩ := LocalH.actual G
  have hB := questBright S t h hp hv hz hy X ht hn hS hk
  have hQ := questCore S t h hp hv hz hy X ht hn
  have hX : Awards (changeCue M S.kernel.penalty N) M' := hB.less hQ (campaign h hy hp t hv hz (inch_pos S.patch.L) hZ).2.1.analytic hb
  have HH := hX i j (-p) p
  change beat _ 0 2 ![relay (-p) i,relay p j]= _ at HH
  rw [neg_add_cancel,if_pos rfl,tune_shop _ hM q hs] at HH
  rw [show beat M' _ _ _= _ from audit_open t h X hp hy hv hz hk hS B T he he' (relay (-p) i) (relay p j)] at HH
  have hx : minusTax T (relay (-p) i)= tune (-p) x := tax_birth T hw (-p) (-q) hs.flip_sign _
  have hl : minusTax T (relay p j)= tune p y := tax_birth T hw p q hs _
  have Hg a b : beat F' 0 2 ![relay (-p) a,relay p b]=(cents c:ℂ)*shop c (hatchTrace U a b q) := trace_emits hp' p q hs a b
  have Hv a b : beat F' 0 2 ![relay p a,relay (-p) b]=(cents c:ℂ)* shop c (hatchTrace U a b (-q)) := by
    have H := trace_emits hp' (-p) (-q) hs.flip_sign a b; rw [neg_neg] at H; exact H
  have Hk a b : beat T' 0 2 ![relay (-p) a,relay p b]=(cents c:ℂ)*shop c (hatchTrace (U.pay U) a b q) := trace_emits hd p q hs a b
  rw [hx,hl,relay_or,relay_or,boardsL,boardsL] at HH
  rw [directing (clears t r R X),directing (clears t r R X),unsung (clouds t r R X)] at HH; simp_rw [directing (clouds t r R X)] at HH
  unfold T' at Hk; unfold F' at Hg Hv
  simp_rw [Hk,Hg,Hv] at HH
  apply mul_left_cancel₀ (a:=(cents c:ℂ)) (by exact_mod_cast cents_pos.ne')
  rw [← HH]; simp only [mul_left_comm _ (cents c:ℂ),← Finset.mul_sum]; ring

lemma stamp_here (p : Site c) (q) (hs : rolls (mon p) q) (j : Loc G 1) (x : Phase (Loc G 0)) :
    let T := carrierY M S.kernel.penalty N
    (∑ i : Loc G 1,(pageD G 0 (-q)*ᵥ x) i*shop c (hatchTrace T (.inl i) (.inr j) q))=0 := by
  classical
  intro T
  let U := tune (-p) x
  have he : _ := wax_off t h X hp hy hv hz hk hS U (relay p j)
  rw [page_read c 0 (-p) (-q) hs.flip_sign x,add_zero,relay_an,boardsR,unsung (clears t r R X)] at he
  have hi := carry_root t h X hp hy hv hz ht hn
  have hx i : beat (clears t r R X) 0 2 ![relay (-p) (Sum.inl i : ScoreBoard G),relay p (.inr j)]= (cents c:ℂ)*shop c (hatchTrace T (.inl i) (.inr j) q) := trace_emits hi p q hs _ _
  simp_rw [hx,mul_left_comm _ (cents c:ℂ),← mul_sum] at he
  exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast cents_pos.ne')
end protocols
end YM.Stationary
end
