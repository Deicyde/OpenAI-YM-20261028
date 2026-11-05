import YM.Next.STATIONARY.Shape.Rank

set_option autoImplicit false
/-!
# Entry frames for the bare (classical) induction. Keep carriers widthstamps
with per-cell units, not the post determinant costs. Actual Hessian exchange
pairs through all legs. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {σ η A C D E τ : ℝ} {c f : Side}

abbrev Atrium (G : Gauge) (P : Patch) := Loc G 1 ⊕ ParcelG G P.L
abbrev GateR (G : Gauge) (S : StepData c f) := Corn (Co c (Atrium G S.patch))

def tourG (G : Gauge) (S : StepData c f) : Point G c f ≃L[ℝ] GateR G S := (((ContinuousLinearEquiv.refl ℝ (Link G c)).prodCongr (directX G S))).trans (wiredFrame c)
def escalade (G : Gauge) (S : StepData c f) : GateR G S →L[ℝ] Bang G c f := ((tourG G S).symm.toContinuousLinearMap).prod 0
def podium (G : Gauge) (S : StepData c f) : GateR G S →L[ℝ] Corn (Co c (Acts G S.patch)) := (pavilionB G S).toContinuousLinearMap ∘L escalade G S
def podiumZ (G : Gauge) (P : Patch) : Phase (Atrium G P) →ₗ[ℂ] Phase (Acts G P) where
    toFun x := Sum.elim (x ∘ Sum.inl) (Sum.elim (x ∘ Sum.inr) 0)
    map_add' a b := by funext i; rcases i with i|(i|i) <;> simp
    map_smul' a b := by funext i; rcases i with i|(i|i) <;> simp

def fining (G : Gauge) (P : Patch) : Phase (Atrium G P) →ₗ[ℂ] Phase (Co P.L (Loc G 1)) := LinearMap.pi fun i=> LinearMap.proj (.inr (.inl i) : Atrium G P)

def redden (G : Gauge) (S : StepData c f) : Phase (Co c (Atrium G S.patch)) →ₗ[ℂ] Phase (Lines G f 1) :=
    LinearMap.pi fun i => let x := unitSplit G S 1 i; LinearMap.proj ((x.1, Sum.inr (.inl x.2)) : Co c (Atrium G S.patch))

def reddish (G : Gauge) (S : StepData c f) : GateR G S→L[ℝ] Link G f :=
    (ContinuousLinearMap.fst ..) ∘L ((ContinuousLinearMap.snd ..) ∘L (tourG G S).symm.toContinuousLinearMap)

lemma redden_true (S : StepData c f) (v : GateR G S) : axes (reddish G S v) = redden G S (axes v) := by
  obtain ⟨x,rfl⟩ := (tourG G S).surjective v
  ext1 i
  have hp : reddish G S (tourG G S x)=x.2.1 := by change ((tourG G S).symm (tourG G S x)).2.1=_; rw [(tourG G S).symm_apply_apply]
  rw [hp]; let y : Co c (Co S.patch.L (Loc G 1)) := unitSplit G S 1 i
  change ((x.2.1 i:ℝ):ℂ)= (directX G S x.2 (y.1,.inl y.2):ℝ)
  rw [show ((y.1,Sum.inl (β:=Loc G 0) y.2):Co _ _) = clothe G S (.inl i) from (inflowL S i).symm,direct_in]; rfl

lemma redden_beaks (S : StepData c f) (p : Site c) (u : Phase (Atrium G S.patch)) : redden G S (tune p u)=poured S.ratio p (fining G S.patch u) := rfl

lemma podium_turns (S : StepData c f) (v : GateR G S) : spinGather (podiumZ G S.patch) (axes v)=axes (podium G S v) := by
  obtain ⟨x,rfl⟩ := (tourG G S).surjective v
  have hp : escalade G S (tourG G S x)=(x,0) := by change ((tourG G S).symm (tourG G S x),0)=_; rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [podium,ContinuousLinearMap.comp_apply,hp]; ext1 i
  rcases i with ⟨i,a|(a|(a|a))⟩
  · rfl
  · rfl
  · change (0:ℂ)=(directX G S 0 (i,a):ℝ); rw [map_zero]; simp
  change (0:ℂ)=(↑(0:ℝ):ℂ); simp

lemma tethers (S : StepData c f) (u : GateR G S) (j) : rehearsal S j (podium G S u)=pianist S j (escalade G S u) := rehearsing S (escalade G S u) j

variable (S : StepData c f) (t : S.Choices)

def centR (p : Clip) (R : PathData G) : GateR G S → ℝ := merit S t p R ∘ (tourG G S).symm

theorem centina (p : Clip) (R : PathData G) (h : S.patch.Branches S.kernel G) : centR S t p R =ᶠ[𝓝 0] (intended p R ∘ reddish G S)+(muralMap S (paperFace false S.kernel.penalty) ∘ podium G S) := by
  let E := escalade G S
  let K := tourG G S
  filter_upwards [(show Tendsto E (𝓝 0) (𝓝 0) by simpa only [map_zero] using E.continuous.tendsto 0).eventually (boom_line S t h false)] with x hx
  let q := K.symm x
  change merit S t p R q=intended _ _ (reddish G S x)+∑ i : Site c,paperFace false S.kernel.penalty (rehearsal S i (podium G S x))
  simp_rw [tethers S x]
  have hh : atire (buffOn S t G false) (headOn S t false (E x)) (E x).2.1 = dress (fedora S t) (Stationary.extend q.2) := by change atire _ _ (0:Vault G c f)=_; rw [atire,extend_zero,one_mul]; rfl
  change tickets S _ (ribbon S t (atire (buffOn S t G false) (headOn S t false (E x)) (E x).2.1))= _ at hx
  rw [hh] at hx
  unfold merit muster; exact congr_arg (intended _ R (reddish G S x) + ·) hx
end YM.Stationary
end

/-!
# Texture dictionary: external arcs plus tall (rough) curve.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {σ η A C D E τ : ℝ} {c f : Side}

def celestial (Φ : Bridge G P) : Eye (Loc G 1) (Atrium G P) := fun p=> {
    toFun v := Sum.elim v (Sum.elim (Φ p *ᵥ v) 0)
    map_add' a b := by ext1 i; rcases i with i|(i|i) <;> simp [Matrix.mulVec_add]
    map_smul' a b := by ext1 i; rcases i with i|(i|i) <;> simp [Matrix.mulVec_smul] }
def scenic (P : Patch) : Phase (ParcelG G P.L)→ₗ[ℂ] Phase (Atrium G P) where
    toFun x := Sum.elim 0 x
    map_add' a b := by ext1 i; rcases i with i|i <;> simp
    map_smul' a b := by ext1 i; rcases i with i|i <;> simp

lemma celestial_flag {Φ : Bridge G P} (h : Poster σ Φ) : Fresh (celestial Φ) σ := by
  refine ⟨fun he hv=> ?_,fun hp v=> ?_⟩
  · apply LinearMap.ext; intro a; simp only [celestial,LinearMap.coe_mk,AddHom.coe_mk,h.shifts he hv]
  refine differentiableAt_pi.mpr (fun i => ?_); rcases i with i | (i|i)
  · exact differentiableAt_const _
  · exact DifferentiableAt.fun_sum (u:= Finset.univ) (fun j _ => (h.shape hp i j).mul_const (v j))
  exact differentiableAt_const _
lemma inject_c (Φ : Bridge G P) p (v) : podiumZ G P (celestial Φ p v)= arriving Φ p v := by ext1 i; rcases i with i|(i|(i|i)) <;> rfl
lemma inject_e (Φ : Bridge G P) p (v) : fining G P (celestial Φ p v)=Φ p *ᵥ v := rfl
lemma inject_g (v : Phase (ParcelG G P.L)) : podiumZ G P (scenic P v)= visibly P false v := by ext1 i; rcases i with i|(i|(i|i)) <;> rfl
lemma inject_t (v : Phase (ParcelG G P.L)) : fining G P (scenic P v)=v ∘ Sum.inl := rfl

def ascentX (S : StepData c f) (W : Matrix (Body 1 f) (Body 1 c) ℝ) : Link G c→L[ℝ] GateR G S := (tourG G S).toContinuousLinearMap ∘L saluteLe W
def torsionX (G : Gauge) (S : StepData c f) : WarpV G S→L[ℝ] GateR G S := (tourG G S).toContinuousLinearMap ∘L ((ContinuousLinearMap.inr ..) ∘L (directX G S).symm.toContinuousLinearMap)

def podiumL (G : Gauge) (P : Patch) : Phase (Acts G P)→ₗ[ℂ] Phase (Atrium G P) := LinearMap.pi fun i=> LinearMap.proj (Sum.elim (fun a=> Sum.inl a) (footVoice G P false) i : Acts G P)
lemma podiumL_in (v : Phase (Atrium G P)) : podiumL G P (podiumZ G P v)= v := by
  ext1 i; rcases i with i|i <;> rfl
lemma podium_doc (S : StepData c f) (x : GateR G S) : spinGather (podiumL G S.patch) (axes (podium G S x)) = axes x := by
  rw [← podium_turns]; ext1 i; rcases i with ⟨i,a|a⟩ <;> rfl

lemma celestial_scene (S : StepData c f) (Φ : Bridge G S.patch) W (h : Premise S W Φ) : Turns (celestial Φ) (ascentX S W) := by
  classical
  obtain ⟨T,hT,hu⟩ := (atlas_photo S h).basis
  refine ⟨spinGather (podiumL G S.patch) ∘ₗ T,fun v=> ?_,fun p q he v=> ?_⟩
  · have he : podium G S (ascentX S W v)= atlasQ S W v := by
      change pavilionB G S (((tourG G S).symm (tourG _ _ _)),0)=_
      rw [ContinuousLinearEquiv.symm_apply_apply]; rfl
    rw [LinearMap.comp_apply, hT, ← he]; exact podium_doc S _
  rw [LinearMap.comp_apply, hu _ _ he,spinMoves, ← inject_c,podiumL_in]
end YM.Stationary
end

/-!
# Merit operators on Atrium. Evaluated simultaneously on shell and subparts.
All τ operations buy width for complex curvature-controlled commitments.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {σ η A C D E τ : ℝ} {c f : Side} {n m : ℕ}
instance (G : Gauge) (P : Patch) : DecidableEq (Atrium G P) := Classical.typeDecidableEq _
instance (G : Gauge) (P : Patch) : DecidableEq (Acts G P) := Classical.typeDecidableEq _

lemma pulseA_add {α : Type} [Fintype α] [DecidableEq α] {f g : Corn α→ℝ} (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) : beat (f+g) 0 n=beat f 0 n+beat g 0 n := by
  apply enlarge_unique; intro v; rw [_root_.add_apply,beat_real,beat_real,beat_real, iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt,_root_.add_apply,Complex.ofReal_add]

abbrev TextS (n : ℕ) (P : Patch) (G : Gauge) := (Fin n → Momentum) → RecordM ℂ (Fin n) (Atrium G P)
variable {ι : Type} [Fintype ι]

def textBare (L : Needle ι (Loc G 1) n) (l : ι → Stitch n) : TextS (n+1) P G := fun p=> (((n+1).factorial:ℂ) • tunnels l L p).compLinearMap (fun _=> fining G P)
def textCap (k : ℝ) (G : Gauge) (n : ℕ) (P : Patch) : TextS n P G := fun p=> (beat (paperFace (P:=P) (G:=G) false k) 0 n).compLinearMap fun j=> imprintsC G P (p j) ∘ₗ podiumZ G P

structure Skimming (S : StepData c f) (U : TextS n S.patch G) (F : GateR G S →ℝ) : Prop where
  beatUp (p : Fin n→ Site c) (q : Fin n→Momentum) (h : ∀ i,rolls (mon (p i)) (q i)) (v : Fin n → Phase (Atrium G S.patch)) :
    beat F 0 n (fun i=> tune (p i) (v i))= if ∑ i,p i=0 then (Fintype.card (Site c):ℂ)* U q v else 0

lemma Skimming.sum (S : StepData c f) {f g : GateR G S→ℝ} {F U : TextS n S.patch G} (h : Skimming S F f) (hp : Skimming S U g) (hv : AnalyticAt ℝ f 0) (hw : AnalyticAt ℝ g 0) : Skimming S (F+U) (f+g) := ⟨fun p q ht v=> by
    rw [pulseA_add hv hw,_root_.add_apply,h.beatUp p q ht v,hp.beatUp p q ht v]
    split; · rw [Pi.add_apply,_root_.add_apply,mul_add]
    simp⟩
lemma Skimming.link {S : StepData c f} {f g : GateR G S→ℝ} {U : TextS n S.patch G} (h : Skimming S U f) (hx : g=ᶠ[𝓝 0] f) : Skimming S U g := ⟨fun p q ht v=> by rw [show beat g 0 n=beat f 0 n by unfold beat; rw [(hx.iteratedFDeriv ℝ n).eq_of_nhds]]; exact h.beatUp p q ht v ⟩

lemma private_text {S : StepData c f} {F : Link G f→ℝ} (L : Needle ι (Loc G 1) n) (l : ι→ Stitch n) (h : Cargo l L F) (hp : Dai L (inch S.patch.L*σ) C) (hs : 0<σ) (hc : AnalyticAt ℝ F 0) : Skimming S (textBare L l) (F∘reddish G S) := by
  refine ⟨fun p q he v=> ?_⟩
  let T := fun j=> fining G S.patch (v j)
  rw [evaluated _ (redden_true S) hc, MultilinearMap.compLinearMap_apply]; simp_rw [redden_beaks]; rw [beat_as_cost, _root_.smul_apply]
  rw [show noteAt _ _ _= _ from cargo_tick S.ratio hp h he hs T]; split; · exact mul_left_comm ((n+1).factorial:ℂ) (Fintype.card (Site c):ℂ) ((tunnels l L q) T)
  simp

lemma scene_currency (S : StepData c f) (h : S.patch.Branches S.kernel G) (k : ℝ) :
    AnalyticAt ℝ (muralMap S (paperFace (G:=G) false k)) 0 ∧ Skimming S (textCap k G n _) (muralMap S (paperFace (G:=G) false k) ∘ podium G S) := by
  let F := paperFace (P:=S.patch) (G:=G) false k
  have hF : ContDiffAt ℝ ω F 0 := ContDiffAt.sum (fun i _ => presents_this h _ _ _)
  have he i : ContDiffAt ℝ ω (F ∘ rehearsal S i) 0 := (show ContDiffAt ℝ ω F (rehearsal S i 0) by rw [map_zero]; exact hF).comp _ (rehearsal S i).contDiff.contDiffAt
  have hm : AnalyticAt ℝ (muralMap S F) 0 := (show ContDiffAt ℝ ω (muralMap S F) 0 from ContDiffAt.sum fun i _=>he i).analyticAt
  refine ⟨hm, ⟨fun p q hv v=> ?_⟩⟩
  rw [evaluated _ (fun u => (podium_turns S u).symm) hm, MultilinearMap.compLinearMap_apply]; simp_rw [spinMoves]; let Y := fun j => podiumZ G S.patch (v j)
  change beat (fun x=>∑ i : Site c,(F ∘ rehearsal S i) x) 0 n (fun i=> tune (p i) (Y i))=_
  rw [beat_summations (n:=n) (s:= Finset.univ) _ (fun i _=> he i)]
  simp_rw [show ∀ i : Site c, beat (F ∘ rehearsal S i) 0 n (fun i=> tune (p i) (Y i))=_ from fun i => audition S p q hv Y i F hF.analyticAt, ← sum_mul]; split
  next hz => rw [hz]; simp [cell]; rfl
  next hz => rw [sum_cell hz,zero_mul]
end YM.Stationary
end

/-!
# Costs for saturated scalar texts. One (nullable) rough, chosen first,
all other constraints smooth. Does not donate arc support. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D E τ : ℝ} {n t c d u : ℕ} {q : Momentum}

structure Pungent (U : TextS n P G) (σ : ℝ) : Prop where
    hol {p : Fin n→ Momentum} (h : ∀ i,p i∈strip σ) (u : Fin n→ Phase (Atrium G P)) : DifferentiableAt ℂ (fun z : (Fin n→Momentum) × (Fin n→ Phase (Atrium G P)) => U z.1 z.2) (p,u)
    shifts p q (h : ∀ i,rolls (p i) (q i)) (he : ∀ i,p i∈strip σ) : U p=U q

lemma Pungent.sum {U Q : TextS n P G} (h : Pungent U σ) (he : Pungent Q σ) : Pungent (U+Q) σ := ⟨fun w u => (h.hol w u).add (he.hol w u),fun p q hv hw=> by rw [Pi.add_apply,Pi.add_apply,h.shifts p q hv hw,he.shifts p q hv hw]⟩

variable {ι : Type} [Fintype ι]
lemma spice_text (L : Needle ι (Loc G 1) n) (l : ι→Stitch n) (h : Dai L (inch P.L*σ) C) (hs : 0<σ) : Pungent (P:=P) (textBare L l) σ := by
  refine ⟨fun {p} hp u=> ?_,fun p q ht hv=> ?_⟩
  · let V := (fining G P).toContinuousLinearMap
    let z := (p,u)
    let X y : Breed n Momentum × (Breed n (Phase (Co P.L (Loc G 1)))) := ((y : (Breed n Momentum) × (Breed n (Phase (Atrium G P)))).1,V ∘ y.2)
    have he : DifferentiableAt ℂ X z := differentiableAt_fst.prodMk (differentiableAt_pi.mpr (fun i => V.differentiableAt.comp (f:=fun b : (Breed n Momentum) × (Breed n (Phase (Atrium G P))) => b.2 i) z (by fun_prop)))
    exact ((tunnels_bill l L h hs (X z) hp).comp z he).const_mul _
  unfold textBare; rw [tunnels_twist l L ht]
lemma spice_scene (k : ℝ) : Pungent (textCap k G n P) σ := by
  refine ⟨fun {p} hp u=> ?_,fun p q ht hv=> ?_⟩
  · let z := (p,u)
    refine differentiableBeat (u:=fun x : (Fin n→Momentum) × (Fin n→ Phase (Atrium G P)) => fun i=> imprintsC G P (x.1 i) (podiumZ G P (x.2 i))) ?_ (beat (paperFace false k) 0 _)
    intro i; exact melody_diff ((podiumZ G P).toContinuousLinearMap.differentiableAt.comp z (f:=fun b : (Fin n→ Momentum) × (Fin n→ Phase (Atrium G P)) => b.2 i) (by fun_prop)) (by fun_prop)
  apply MultilinearMap.ext; intro v; unfold textCap; rw [MultilinearMap.compLinearMap_apply,MultilinearMap.compLinearMap_apply]; simp_rw [LinearMap.comp_apply, flips_melody _ (ht _)]

-- selection of energies first slot. Smooth Herm inputs others independently.

def AtomicR (Φ : Bridge G P) (v : Phase (Atrium G P)) (q : Momentum) : Prop := ∃ t,v=celestial Φ q (Pi.single t 1)
-- variable number of smooth legs; first rough capability.
structure Laureate (U : TextS (n+1) P G) (Φ : Bridge G P) (σ C : ℝ) : Prop where
    fund : 0 ≤ C
    plain (p : Breed n Momentum) (hp : ∀ i,p i∈strip σ) (v : Breed n (Phase (Atrium G P))) (he : ∀ i,AtomicR Φ (v i) (p i)) : ‖U p v‖ ≤ C
    peak (p : Breed n Momentum) (hp : ∀ i,p i∈strip σ) (v : Fin n→Phase (Atrium G P)) (he : ∀ i,AtomicR Φ (v i) (p i.succ)) (u : Phase (ParcelG G P.L)) (hx : (slabW G P.L).rate (p 0) u≤1) : ‖U p (Fin.cons (scenic P u) v)‖ ≤ C
lemma Laureate.sum {U Q : TextS (n+1) P G} {Φ : Bridge G P} (h : Laureate U Φ σ C) (hp : Laureate Q Φ σ A) : Laureate (U+Q) Φ σ (C+A) :=
    ⟨add_nonneg h.fund hp.fund,fun p hv u w=> le_trans (norm_add_le _ _) (add_le_add (h.plain p hv u w) (hp.plain p hv u w)),fun p hv u w a z=> (norm_add_le _ _).trans (add_le_add (h.peak p hv u w a z) (hp.peak p hv u w a z))⟩
section ps
variable {Φ : Bridge G P} (h : Cruise Φ c σ D)
include h
lemma panel_plain (p : Momentum) (he : p∈strip σ) {v : Phase (Atrium G P)} (hv : AtomicR Φ v p) (l : List Axis) (hx : l.length≤c) (j : Loc G 1) :
    Hearing (balcony _) 0 (fun z : Site P.L=> flight p l (fining G P v) (z,j)) (inch P.L^(1+l.length)*ruffle D) := by
  have hi := inch_pos P.L; have hh := h.2.1; obtain ⟨i,rfl⟩ := hv
  rw [inject_e]; exact Hearing.sup (mul_nonneg (pow_nonneg hi.le _) (ruffled hh)) (fun z => (h.2.2 l hx p he i _).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (pow_nonneg hi.le _)))
lemma panel_rough (p : Momentum) (he : p∈strip (1:ℝ)) {u : Phase (ParcelG G P.L)} (hx : (slabW G P.L).rate p u≤1) (l : List Axis) (ht : l.length≤1) (j : Loc G 1) :
    Hearing (balcony _) 1 (fun z : Site P.L=> flight p l (fining G P (scenic P u)) (z,j)) (inch P.L^(1+l.length)*ruffle D) := by
  have hi := Slab.serial_at (q:=p) (serial_butt (altarTile P.L (Loc G 1)) (Slab.basic (Loc G 0))) u
  rw [sliceX,one_mul] at hi; rw [inject_t]; exact (lower_voice he (hi.trans hx) l ht j).more (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h.2.1) (pow_nonneg (inch_pos _).le _))

def giftBay (G : Gauge) (t : ℕ) (ι : Type) [Fintype ι] (D σ C : ℝ) := ((t+1).factorial:ℝ)*roundBay G t ι C σ (ruffle D^(t+1))
lemma velvet_text (L : Needle ι (Loc G 1) n) (l : ι→Stitch n) (hs : 0<σ) (ht : σ≤1) (hc : 0≤C) (hp : Dai L (inch P.L*σ) C)
    (hd : ∀ a, (n+1)+∑ j,(l a j).length=4+u) (he : ∀ a j,(l a j).length≤c) (hr : ∀ a,(l a 0).length ≤1) :
    Laureate (textBare L l) Φ σ (inch P.L^u*giftBay G n ι D σ C) := by
  let C' := ruffle D
  let X := ruffle D^(n+1); let V := giftBay G n ι D σ C
  let K (a : ι) (j) := inch P.L^(1+(l a j).length)*C'
  have hx := inch_pos P.L; have hy : 0≤X := pow_nonneg (ruffled h.2.1) _
  have hf p (v : Breed n (Phase (Atrium G P))) (w : ∀ i,p i∈strip σ) (A : Breed n ℕ) (hw : ∑ i,A i≤ 2) (hv : ∀ a i j,Hearing (balcony _) (A i) (fun z : Site P.L => flight (p i) (l a i) (fining G P (v i)) (z,j)) (K a i)) : ‖textBare L l p v‖ ≤ inch P.L^u * V := by
    have he := tunnels_book l L hp hs w (fining G P∘v) K hv hw hc (fun a => (needleCollapse (l a) u C' P.L (hd a)).le)
    have hh : ‖textBare L l p v‖= ((n+1).factorial:ℝ)*‖tunnels l L p (fining G P ∘ v)‖ := by change ‖((n+1).factorial:ℂ) * _‖=_; rw [norm_mul,Complex.norm_natCast]; rfl
    rw [hh]; exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by unfold V giftBay roundBay C'; ring)
  refine ⟨mul_nonneg (by positivity) (mul_nonneg (by positivity) (rip_room G n ι σ C X hc hy)),fun p h u z => ?_,fun p W t HT u hu => ?_⟩
  · rename_i h'
    exact hf p u h (fun _=>0) (by simp) (fun a i j => panel_plain h' _ (h _) (z _) _ (he _ _) _)
  apply hf p _ W (Fin.cons 1 (fun _ : Fin n=>0)) (by rw [Fin.sum_univ_succ]; simp)
  intro a i j
  cases i using Fin.cases
  · exact panel_rough h _ (fun j => (W 0 j).trans_le ht) hu _ (hr _) j
  next i => simp only [Fin.cons_succ]; exact panel_plain h _ (W i.succ) (HT i) _ (he _ _) _
end ps
end YM.Stationary
end

/-!
# Stamps for true merit, all scales. Follows schedule with cost inherited
multiplying A (repβ not charged). Pre-L lifts separate.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D E τ k B : ℝ} {n t u : ℕ} {q : Momentum}

section c
variable {Φ : Bridge G P}

def napTax (G : Gauge) (j n : ℕ) (σ D : ℝ) := (2:ℝ)^(n+1)*(4*|cashBook G j (n+1) (muralRoom j*cabinTicket G D) σ|)
lemma nap_cap (k) (h : Cruise Φ t σ D) (he : P.Branches K G) (hp : σ≤1) : Laureate (textCap k G (n+1) P) Φ σ (napTax G P.J n k D) := by
  let H := h.stars hp
  let C := cabinTicket G D
  let T := StaffP G P (muralRoom P.J*C)
  let X := cashBook G P.J (n+1) (muralRoom P.J*C) k
  have hx (p : Momentum) (u : Phase (Atrium G P)) (he : AtomicR Φ u p) (ht : p∈strip σ) : Shiny T (imprintsC G P p (podiumZ G P u)) 0 := by
    obtain ⟨i,rfl⟩ := he; rw [inject_c]; exact shiny_steps _ (H.paint i _ ht) (H.brighten ht)
  let Y p (u : Phase (Atrium G P)) := imprintsC G P p (podiumZ G P u)
  have ha : Gallop (balcony Unit) T (fun _ => paperFace false k) (n+1) (4*|X|) := by
    have hn := books_paid (A:=balcony Unit) (n:=n+1) he (weight_staff H) k
    simpa only [Finset.sum_const,card_univ,show Fintype.card Axis=4 from rfl,nsmul_eq_mul,Nat.cast_ofNat] using! Gallop.fixedsum (M:=fun j _ x => presentsBox false k x j) (K:=fun _ : Axis => |X|) (fun i => (hn i).raises le_rfl (le_abs_self _))
  have hv (p : Fin (n+1)→Momentum) u (R : Fin (n+1)→ℕ) (hp : ∑ i,R i ≤ 2) (he : ∀ i, Shiny T (Y (p i) (u i)) (R i)) :
      ‖textCap k G (n+1) P p u‖≤napTax G P.J n k D := by
    have hk := (through_charge (ha.reaches _ (Nat.zero_lt_succ _) le_rfl) he hp).rasp hp
    change ‖beat (paperFace false k) 0 (n+1) (fun i => Y (p i) (u i))‖ ≤ (2:ℝ)^(n+1)*(4*|X|)
    simpa using hk
  refine ⟨by unfold napTax; positivity,fun p hp u hr => hv p u _ (show ∑ _ : Fin (n+1),(0:ℕ) ≤ 2 by simp) (fun i => hx _ _ (hr i) (hp _)),fun p ht u hw v hq=> ?_⟩
  apply hv p _ (Fin.cons (1:ℕ) (fun _ => 0)) (by rw [Fin.sum_univ_succ]; simp)
  intro i; cases i using Fin.cases
  · simp only [Y,Fin.cons_zero,inject_g]; exact shiny_steps _ (store_mono (seen_affect (P:=P) false (H.brighten (ht 0)) hq) H.price) (H.brighten (ht 0))
  next i => simp only [Fin.cons_succ]; exact hx _ _ (hw i) (ht _)

-- compressed on smooth prices. Include res cost datum independent L.
variable {ι : Type} [Fintype ι]
end c

section pledge
variable {m g : ℕ→Side}

lemma velvet_sized (L : Needle (Ports n t) (Loc G 1) n) {Φ : Bridge G P} (h : Cruise Φ 2 σ D) (hs : 0<σ) (hw : σ ≤ 1) (ht : Dai L (inch P.L*σ) C) (hc : 0≤C) (he : t≤2) (hz : (n+1)+t=4+u) :
    let U := textBare (P:=P) L (winglet n t)
    Pungent U σ ∧ Laureate U Φ σ (inch P.L^u * giftBay G n (Ports n t) D σ C) := by
  intro U
  exact ⟨spice_text _ _ ht hs, velvet_text h _ _ hs hw hc ht (fun a => by unfold winglet; rw [roller_extent]; exact hz) (fun a i=> (roller_ge _ _ _).trans he) (fun a=> by rw [winglet_port]; exact Nat.zero_le _)⟩

lemma voile (G : Gauge) (t n : ℕ) (σ : ℝ) (hs : 0<σ) : ∃ η k, 0<η ∧ 0 ≤ k ∧ ∀ A, 0≤A → ∀ (m : ℕ→Side) (U : ∀ i,Link G (m i)→ℝ), Drinkable t m U n σ A →
    ∃ K : Needle (Ports t n) (Loc G 1) t,Dai K η (A*k) ∧ ∀ i, Cargo (winglet t n) K (U i) := by
  obtain ⟨η,K,h,hK,H⟩ := winding (G:=G) t n hs
  refine ⟨η,K,h,hK,fun A hA m U hp=> ?_⟩
  obtain ⟨X,hX,hx⟩ := hp
  obtain ⟨Y,hY,V⟩ := H A hA X hx
  exact ⟨Y,hY,fun i=> spooling h V hY (hX i)⟩

end pledge
end YM.Stationary
end

/-!
# Assemble the specialty texts for the two campaign vertices, prices
 BEFORE stamp. Next PUNGENT aperture accounts. No β assumptions.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ η A C D E τ : ℝ} {t n u J : ℕ} {p : Clip} {R : PathData G} {m g : ℕ → Side}
lemma Laureate.thin {Φ : Bridge G P} {U : TextS (n+1) P G} (h : Laureate U Φ σ C) (he : η ≤ σ) (hp : C≤E) : Laureate U Φ η E := ⟨h.fund.trans hp,fun p w v ht => (h.plain p (fun i j => (w i j).trans_le he) v ht).trans hp,fun p w t ht u z=> (h.peak p (fun i j => (w i j).trans_le he) t ht u z).trans hp ⟩

lemma ageGlimpse {X M C' D'} (h : R.Bounds p σ X A) (F : Armada m g P K) (b : ∀ i,(F.boot i).Choices) (hp : P.Branches K G) (Φ : Bridge G P) (hf : Cruise Φ 2 η D) (hs : 0<η) (ht : η≤1) {Q : Needle (Ports n t) (Loc G 1) n} {U : Needle (Ports n u) (Loc G 1) n} (he : Dai Q (inch P.L*η) C) (hq : Dai U (inch P.L*η) M) (hQ : ∀ i,Cargo (winglet n t) Q (WilsonQ G (g i))) (hU : ∀ i,Cargo (winglet n u) U ((intended p R (m:=g i)-WilsonQ G (g i)))) (hC : 0≤C) (hM : 0≤M)
    (h2 : (n+1)+t=4) (h3 : (n+1)+u=5) (h4 : t ≤ 1) (h5 : u≤ 2) (hx : P.J=J)
    (hp' : giftBay G n (Ports n t) D η C+napTax G J n K.penalty D≤ C') (hw : giftBay G n (Ports n u) D η M≤D') :
    ∃ T : TextS (n+1) P G, Pungent T η ∧ Laureate T Φ η (C'+inch P.L*D') ∧ ∀ i, Skimming (F.boot i) T (centR (F.boot i) (b i) p R) := by
  let V : TextS (n+1) P G := textBare Q (winglet _ _)
  let W : TextS (n+1) P G := textBare U (winglet _ _)
  let Y := textCap K.penalty G (n+1) P
  obtain ⟨hV,hE⟩ := velvet_sized Q hf hs ht he hC (by omega) (show (n+1)+t=4+0 from h2)
  obtain ⟨hW,hH⟩ := velvet_sized U hf hs ht hq hM h5 (show (n+1)+u=4+1 from h3)
  have hP : Pungent Y η := spice_scene K.penalty
  have hY := (hE.sum hH).sum (nap_cap K.penalty hf hp ht (n:=n))
  rw [pow_zero,one_mul, pow_one] at hY
  refine ⟨V+W+Y,(hV.sum hW).sum hP,hY.thin le_rfl (by rw [hx]; nlinarith only [hw,hp',inch_pos P.L]),fun i=> ?_⟩
  let S := F.boot i; let L := reddish G S
  let α := WilsonQ G (g i); let β := (intended p R (m:=g i)-WilsonQ G (g i))
  have hα : AnalyticAt ℝ α 0 := Wilson_witness.analytic
  have hβ : AnalyticAt ℝ β 0 := (strain _ _ h).analytic.sub hα
  have hh : Skimming S (V+W) ((α∘ L)+(β∘ L)) := by
    apply Skimming.sum S (private_text (S:=S) _ _ (hQ i) he hs hα) (private_text (S:=S) _ _ (hU i) hq hs hβ)
    · exact AnalyticAt.comp (g:=α) ((L.map_zero).symm ▸ hα) (L.analyticAt _)
    exact AnalyticAt.comp (g:=β) ((L.map_zero).symm ▸ hβ) (L.analyticAt _)
  have hI : intended p R (m:=g i)∘ L=(α∘ L)+(β∘ L) := by
    ext x; change intended p R (L x) = WilsonQ _ _ (L x)+(intended p R (L x) - WilsonQ _ _ (L x)); abel
  rw [← hI] at hh
  obtain ⟨h₁,h₂⟩ := scene_currency S hp (n:=n+1) K.penalty
  apply Skimming.link (hh.sum S h₂ ?_ ?_) (centina S (b i) p R hp)
  · apply AnalyticAt.comp _ (L.analyticAt _); rw [L.map_zero]; exact (strain _ _ h).analytic
  exact AnalyticAt.comp (g:=muralMap _ _) (f:=podium G S) ((podium G S).map_zero.symm ▸ h₁) ((podium G S).analyticAt _)

section bottom
lemma setWest (G : Gauge) (w η Q Z D ε : ℝ) (hσ : 0<w) (hη : 0<η) (hw : η ≤ 1) (hz : 0≤Z) (hQ : 0≤Q)
    (J : ℕ) (K : KernelChoices) : ∃ a b : ℝ, 0≤a ∧ 0≤b ∧ ∀ σ A, 0<σ → 0 ≤ A → ∃ σ' ℓ r:ℝ, 0 < σ' ∧ 0≤ℓ ∧ 0≤r ∧ ∀ (m n : ℕ→Side), Tendsto (fun i => (n i).val) atTop atTop → ∀ (p : Clip) (R : PathData G) (B : Bed) (Λ : ℝ), p.direct ≤ Z → R.Bounds p σ A Λ → Attached B R → B.metric.strip w Q → (∀ i, Floor B p i ε Q) → (∀ i, Bid.Sworn B (n i) G) →
      ∀ (P : Patch), P.J=J → P.Branches K G → inch P.L*η ≤ σ' → ∀ (F : Armada m n P K) (t : ∀ i,(F.boot i).Choices) (Φ : Bridge G P), Cruise Φ 2 η D →
    ∃ T : TextS 3 P G, ∃ U : TextS 4 P G, Pungent T η ∧ Pungent U η ∧ Laureate T Φ η (a+inch P.L*ℓ) ∧ Laureate U Φ η (b+inch P.L*r) ∧ ∀ i, Skimming (F.boot i) T (centR (F.boot i) (t i) p R) ∧ Skimming (F.boot i) U (centR (F.boot i) (t i) p R) := by
  obtain ⟨B,hB,H⟩ := whiteWilson G
  obtain ⟨u,Mτ,hu,hτ,H₁⟩ := voile G 2 1 1 zero_lt_one
  obtain ⟨v,N,hv,hN,H₂⟩ := voile G 3 0 1 zero_lt_one
  let a := |giftBay G 2 (Ports 2 1) D η (B*Mτ)+napTax G J 2 K.penalty D|
  let b := |giftBay G 3 (Ports 3 0) D η (B*N)+napTax G J 3 K.penalty D|
  refine ⟨a,b,abs_nonneg _,abs_nonneg _,fun σ A hs he => ?_⟩
  obtain ⟨y,P,hy,hP,V⟩ := greyson G w ε Q Z σ A hσ hQ hz hs he
  obtain ⟨z,Zτ,hz₀,hzc,V₁⟩ := voile G 2 2 y hy
  obtain ⟨r,E',hr,hE,V₂⟩ := voile G 3 1 y hy
  let ℓ := |giftBay G 2 (Ports 2 2) D η (P*Zτ)|; let T:=|giftBay G 3 (Ports 3 1) D η (P*E')|
  refine ⟨min (min u v) (min z r),ℓ,T,lt_min (lt_min hu hv) (lt_min hz₀ hr),abs_nonneg _,abs_nonneg _,fun m n hm p R G' Λ hp ht ha hk hg hT S hS hX hC F t Φ hΦ => ?_⟩
  have hx := H n hm
  have hL := V n hm G' p R Λ ht ha hk hp hg hT
  obtain ⟨Q₁,M₁,L₁⟩ := H₁ B hB n _ (hx _ (show 2>0 by decide) (by decide))
  obtain ⟨Q₂,M₂,L₂⟩ := H₂ B hB n _ (hx _ (show 3>0 by decide) (by decide))
  obtain ⟨Q₃,M₃,L₃⟩ := V₁ _ (hP) n _ (hL _ (show 2>0 by decide) (by decide))
  obtain ⟨Q₄,M₄,L₄⟩ := V₂ _ (hP) n _ (hL _ (show 3>0 by decide) (by decide))
  -- Ψ holds contested tangent at width.
  have hC₁ : inch S.L*η ≤ min u v := hC.trans (min_le_left ..); have hC₂ : inch S.L*η ≤ min z r := hC.trans (min_le_right ..)
  obtain ⟨Q,h1,h2,h3⟩ := ageGlimpse ht F t hX Φ hΦ hη hw (fun i j=> (M₁ i j).mono (hC₁.trans (min_le_left ..)) le_rfl) (fun i j => (M₃ i j).mono (hC₂.trans (min_le_left ..)) le_rfl) L₁ L₃ (by positivity) (by positivity) (by decide) (by decide) (by decide) (by decide) hS (le_abs_self _) (le_abs_self _)
  obtain ⟨P,h4,h5,h6⟩ := ageGlimpse ht F t hX Φ hΦ hη hw (fun i j => (M₂ i j).mono (hC₁.trans (min_le_right ..)) le_rfl) (fun i j => (M₄ i j).mono (hC₂.trans (min_le_right ..)) le_rfl) L₂ L₄ (by positivity) (by positivity) (by decide) (by decide) (by decide) (by decide) hS (le_abs_self _) (le_abs_self _)
  exact ⟨Q,P,h1,h4,h2,h5,fun i=> ⟨h3 i,h6 i⟩⟩
end bottom
end YM.Stationary
end
