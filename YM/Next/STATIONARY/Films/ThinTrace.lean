import YM.Next.STATIONARY.Films.Site

set_option autoImplicit false
/-!
# Γ=TON + T-profile. T^9 transport bookkeeping. Corresponds in any
mesh here, only Tune receipts. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype ι] [DecidableEq ι] {G : Gauge} {c f L : Side} {P : Patch} {C D σ μ : ℝ} {p q : Momentum}

-- Real reindex on inverse/pow etc.
lemma repack_scale (a : α≃β) (b : γ≃δ) (U : Matrix α γ ℝ) (c : ℝ) : repackM a b (c • U)= c • repackM a b U := rfl
lemma repack_scale_inv (e : α≃β) (u : Matrix α α ℝ) (h : IsUnit u.det) : repackM e e u⁻¹=(repackM e e u)⁻¹ := by
  let T := repackM e e u
  have he : T* repackM e e u⁻¹=1 := by rw [show T=_ from rfl,← repack_multiply e _,Matrix.mul_nonsing_inv _ h,repack_unit]
  change _=T⁻¹
  have hv : IsUnit T.det := by rw [show T=_ from rfl,repack_det]; exact h
  exact ((Matrix.nonsing_inv_mul_cancel_left T _ hv).symm.trans ((congr_arg (T⁻¹ *·) he).trans (Matrix.mul_one _)))

section triple
variable (F : Film ι α α)
def tripleFilm := (F.pay F).pay F
lemma tripleBase (p) : (tripleFilm F).tab p=(F.tab p)^3 := by rw [pow_succ,sq]; rfl
lemma triple_am (Q : OperatorF ι c α α) (h : Ticket F Q) : Ticket (tripleFilm F) (fun x => Q x^3) := by
  refine Ticket.foreign ((h.pay h).pay h) ?_; filter_upwards with i; rw [pow_succ,sq]
lemma triple_act (h : Charges (Slab.basic _) (Slab.basic _) F σ C) (he : 0<σ) : Charges (Slab.basic _) (Slab.basic _) (tripleFilm F) σ (4*(4*C*C)*C) := ((h.pay h he).pay h he)
lemma triple_paid (h : Play F σ) : Play (tripleFilm F) σ := (h.pay h).pay h
end triple

section tonic
variable (E : Eye ι (Acts G P))

def tonFilm := (sectorMail P E).rear.pay (sectorMail P E)
def amFilm := (tonFilm E).plus (Film.cardF (ι:=ι) (fun _ : Momentum => ((inch P.L)^2:ℝ) • (1:CompM (Co P.L (Loc G 0)) _)))
def pebFilm := ((amFilm E).back).weight (((inch P.L)^2:ℝ):ℂ)
def cannonFilm := (tripleFilm (tripleFilm (pebFilm E))).weight (((inch P.L)^2:ℝ):ℂ)
def grenadeFilm := (tonFilm E).plus (cannonFilm E)
lemma rear_tone {p} : (sectorMail P E).tab p=areaRef G P.L p := by simp [sectorMail, Film.plus,Dapper.base,Film.pay, stableF, Film.cardF]
end tonic

variable (S : StepData c f) (t : S.Choices) (r : Bool) (Z : Corn (Co c ι)→L[ℝ] Bang G c f) {D : Eye ι (Acts G S.patch)}
    (h : Turns D (billZ S Z))
def headingF x := (headOn S t r (Z x)).1
include h
lemma ton_rears : Ticket (tonFilm D) (fun x => repackM (unitSplit G S 0) (unitSplit G S 0) (tonic (headingF S t r Z x))) := by
  classical
  have he := mail_for S Z h t r
  refine Ticket.foreign (he.rear.pay he) ?_; filter_upwards with x
  let U := mail (headingF S t r Z x)
  change _=repackM _ _ (Uᵀ*U)
  have hx : repackM (unitSplit G S 0) (unitSplit G S 0) (Uᵀ*U)=_ := repack_multiply _ (unitSplit G S 1) ..
  exact hx.symm
lemma amo_reel : Ticket (amFilm D) (fun x => repackM (unitSplit G S 0) (unitSplit G S 0) (ammo (inch S.patch.L) (headingF S t r Z x))) := by
  classical
  let T := ton_rears S t r Z h
  let R : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  let μ := inch S.patch.L
  let Q : Matrix (Lines G f 0) (Lines G f 0) ℝ := μ^2 • 1
  have he : Jaunt (approached (repackM R R Q)) (fun _ => (μ^2:ℝ) • (1:CompM (Co S.patch.L (Loc G 0)) _)) 0 := by
    unfold Q; rw [repack_scale,repack_unit,prom_tone]
    have hz : approached (1:Funds (Co c (Co S.patch.L (Loc G 0))))=1 := by ext i j; by_cases h : i=j <;> simp [approached,Matrix.one_apply, *]
    rw [hz]; exact Jaunt.smul Jaunt.noop _
  exact T.plus (Ticket.current _ _ he)
lemma peb_reel : Ticket (pebFilm D) (fun x => repackM (unitSplit G S 0) (unitSplit G S 0) (pebble (inch S.patch.L) (headingF S t r Z x))) := by
  classical
  let Zr : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  let μ := inch S.patch.L
  let F x := ammo μ (headingF S t r Z x)
  let M := fun x => repackM Zr Zr (F x)
  have hp x : IsUnit ((M x).det) := by rw [show M x=repackM _ _ _ from rfl,repack_det]; exact fund_det (ammo_safe _ (inch_pos _))
  let H : Ticket (amFilm D).back (fun x => (M x)⁻¹) := (amo_reel S t r Z h).back (hp 0)
  refine (H.weight (μ^2)).foreign ?_; filter_upwards with x
  change μ^2 • _=repackM Zr Zr (μ^2 • (F x)⁻¹)
  rw [repack_scale,repack_scale_inv]
  exact fund_det (ammo_safe _ (inch_pos _))
lemma fuel_reel : Ticket (cannonFilm D) (fun x => repackM (unitSplit G S 0) (unitSplit G S 0) (cannon (inch S.patch.L) (headingF S t r Z x))) := by
  classical
  let μ := inch S.patch.L
  let F x := pebble μ (headingF S t r Z x)
  let Ry : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  let M x := repackM Ry Ry (F x)
  have H := triple_am _ (fun x => (M x)^3) (triple_am _ M (peb_reel S t r Z h))
  refine (H.weight (μ^2)).foreign ?_; filter_upwards with x
  have he n : M x^n=repackM Ry Ry ((F x)^n) := by
    induction n with
    | zero => rw [pow_zero, pow_zero,repack_unit]
    | succ n ih => rw [pow_succ,pow_succ, ih,repack_multiply _ Ry]
  change μ^2 • (M x^3)^3=repackM Ry Ry (μ^2 • (F x)^9)
  rw [← pow_mul,he,repack_scale]
lemma shipGren : Ticket (grenadeFilm D) (fun x => repackM (unitSplit G S 0) (unitSplit G S 0) (grenade (inch S.patch.L) (headingF S t r Z x))) :=
    (ton_rears S t r Z h).plus (fuel_reel S t r Z h)
end YM.Stationary
end

/-!
# Common centers of static films. Real mesh of an arbitrary size m used
only to fix area/second-order comparison at the trivial field. No extension
or disambiguation of actual branch kernels. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] {G : Gauge} {c f L : Side} {P : Patch} {C σ μ : ℝ} {p : Momentum} (E : Eye ι (Acts G P))
lemma ton_ground (hs : p∈strip σ) : (tonFilm E).tab p=furnish P.L (fun p => stone p • (1:CompM (Loc G 0) (Loc G 0))) p := by
  let M := areaRef G P.L
  let K q := (M (-q))ᵀ * M q
  have hz : (tonFilm E).tab=K := by funext p; simp only [K, M, tonFilm, Film.pay, Film.rear,rear_tone]
  rw [hz]
  have hh : Poster σ K := ((areaNice ..).reverse.forge (areaNice G P.L))
  have hW : Poster σ (furnish P.L (fun p => stone p • (1:CompM (Loc G 0) (Loc G 0)))) := by
    have hx := (ammo_poster (G:=G) (μ:=0) (σ:=inch P.L*σ)); apply Poster.furnish_ok
    simpa only [soda,Complex.ofReal_zero,zero_pow two_ne_zero, add_zero] using hx
  have hσ : 0<σ := (abs_nonneg _).trans_lt (hs 0)
  apply Poster.renew hh hW hσ walentes _ hs
  intro i
  let m := walent i
  let f : Side := m*P.L
  let S : StepData m f := ⟨P,⟨1,1,1,1,zero_lt_one,zero_lt_one,zero_lt_one,zero_lt_one⟩,rfl⟩
  let T : Lines G f 0≃ Co m (Co P.L (Loc G 0)) := unitSplit G S 0
  let Y : Lines G f 1≃ Co m (Co P.L (Loc G 1)) := unitSplit G S 1
  let U := mail (1:Config G f); let F := approached (repackM Y T U)
  refine ⟨Fᵀ*F,((zero_neat G S).takes.hoist (zero_neat G S)), ?_⟩
  rw [show Fᵀ*F=approached (repackM T T (Uᵀ*U)) by rw [repack_multiply _ Y, repack_rotate,prom_mul]; rfl]
  change Jaunt ((approached (tonic (1:Config G f))).submatrix _ _) _ _
  refine Jaunt.press S.ratio (tonic_symbol (G:=G) f) (σ:=1) ?_ zero_lt_one
  simpa only [soda,Complex.ofReal_zero,zero_pow two_ne_zero, add_zero] using ammo_poster (G:=G) (μ:=0) (σ:=inch S.ratio.count*1)

section furniture
variable {K T : Momentum→CompM α β}
lemma furnish_add : furnish L (K+T) p=furnish L K p+furnish L T p := by
  have he : posterBlock L (K+T) p=posterBlock L K p+posterBlock L T p := by ext; simp [posterBlock,fiber]; split <;> simp
  unfold furnish; rw [he, Matrix.mul_add, Matrix.add_mul]
lemma furnish_one : furnish L (fun _ => (1:CompM α α)) p=1 := by
  have ht : posterBlock L (fun _ => (1:CompM α α)) p=1 := by ext ⟨i,a⟩ ⟨j,b⟩; by_cases h : i=j <;> simp [posterBlock,fiber,h,Matrix.one_apply]
  unfold furnish; rw [ht, Matrix.mul_one,mul_nonsing_inv _ (tile_solid p)]
lemma furnish_mol (x : ℂ) : furnish L (x • K) p=x • furnish L K p := by
  have h : posterBlock L (x • K) p=x • posterBlock L K p := by ext; simp only [posterBlock,fiber,Matrix.of_apply,Pi.smul_apply,Matrix.smul_apply]; split <;> simp
  unfold furnish; rw [h,Matrix.mul_smul,Matrix.smul_mul]

lemma furnish_prod {F M : Momentum→CompM α α} : furnish L (fun p => F p*M p) p=furnish L F p*furnish L M p := by
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro v; change furnish _ _ _*ᵥ v= _*ᵥ v
  rw [← alias_pack p v, Matrix.mulVec_sum,Matrix.mulVec_sum]; refine sum_congr rfl fun x _ => ?_
  rw [furnish_gear, ← Matrix.mulVec_mulVec _ (furnish _ F p), furnish_gear, furnish_gear,mulVec_mulVec]
end furniture

lemma amc_ground (hs : p∈strip σ) : (amFilm E).tab p= furnish P.L (fun p => soda (inch P.L) p • (1:CompM (Loc G 0) (Loc G 0))) p := by
  let c := inch P.L
  simp only [amFilm,Film.plus, Pi.add_apply,Film.cardF,ton_ground E hs]; unfold soda; simp_rw [add_smul]
  let F q := stone q • (1:CompM (Loc G 0) (Loc G 0))
  let M := fun _ : Momentum => (1:CompM (Loc G 0) (Loc G 0))
  change furnish _ F p+_ = furnish _ (F+(c:ℂ)^2 • M) p
  rw [furnish_add,furnish_mol,show furnish P.L M p=1 from furnish_one, ← Complex.ofReal_pow]; rfl

lemma peb_ground (hs : p∈strip (1/128:ℝ)) : (pebFilm E).tab p=furnish P.L (fun p => damp (inch P.L) p • (1:CompM (Loc G 0) (Loc G 0))) p := by
  let c := inch P.L
  let F q := soda c q • (1:CompM (Loc G 0) (Loc G 0)); let X := furnish P.L F p
  let T q := (soda c q)⁻¹ • (1:CompM (Loc G 0) (Loc G 0))
  let Y := furnish P.L T p
  have hx : X⁻¹=Y := by
    apply inv_eq_right_inv; apply Matrix.toLin'.injective; apply LinearMap.ext; intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply,Matrix.one_mulVec]; rw [← alias_pack p v, mulVec_sum]; refine sum_congr rfl fun i _ => ?_
    unfold X Y; rw [← Matrix.mulVec_mulVec _ (furnish _ F p), furnish_gear, furnish_gear];
    have he : soda c (aliasAt p i)≠0 := soda_glass (inch_pos _) (inch_le _) (alias_inside hs i)
    simp only [F,T,Matrix.smul_mulVec,Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ he, one_smul]
  simp only [pebFilm,Film.weight, Pi.smul_apply,Film.back,Film.coupon]; rw [amc_ground _ hs, show _⁻¹=Y from hx, Complex.ofReal_pow]; unfold damp Y; rw [← furnish_mol]; congr 2; ext1 i; rw [Pi.smul_apply]; exact smul_smul ..
lemma peb_triple (hs : p∈strip (1/128:ℝ)) : (tripleFilm (pebFilm E)).tab p=furnish P.L (fun p => damp (inch P.L) p ^ 3 • (1:CompM (Loc G 0) (Loc G 0))) p := by
  rw [tripleBase,peb_ground _ hs, pow_succ,sq,← furnish_prod, ← furnish_prod]; congr 2
  ext1 i; rw [Matrix.mul_smul,Matrix.mul_smul,mul_one,smul_smul,Matrix.mul_one,smul_smul]; rw [mul_comm,pow_succ,sq,mul_assoc]
lemma cannon_ground (hs : p∈strip (1/128:ℝ)) : (cannonFilm E).tab p=furnish P.L (fun p => satin (inch P.L) p • (1:CompM (Loc G 0) (Loc G 0))) p := by
  simp only [cannonFilm,Film.weight,Pi.smul_apply,tripleBase (tripleFilm ..),peb_triple _ hs,pow_succ _ 2,sq]
  rw [← furnish_prod,← furnish_prod, ← furnish_mol]; congr 2; ext1 i; rw [Pi.smul_apply,Matrix.mul_smul,Matrix.mul_smul,Matrix.mul_one,smul_smul,Matrix.mul_one, smul_smul,smul_smul]; congr 1; unfold satin; push_cast; ring
lemma grenade_ground (hs : p∈strip (1/128:ℝ)) : (grenadeFilm E).tab p=throneK G P.L p := by
  rw [grenadeFilm, Film.plus]; simp only [Pi.add_apply, ton_ground _ hs,cannon_ground _ hs,← furnish_add]; congr 1
  ext1 i; rw [Pi.add_apply, ← add_smul]; rfl
end YM.Stationary
end

/-!
# Trace phase ideal for differentiated scattering. `triple_charge` crucial:
ALL routes have at most two differentiated legs. r.f.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] {G : Gauge} {L : Side} {P : Patch} {C D B σ : ℝ} {p q : Momentum}
namespace Ledger
variable {X : Slab α} {Y : Slab β} {Z : Slab γ} {F L : Film ι α β} {G : Film ι β γ}
lemma credit (h : Ledger X Y F σ C) (he : 0<σ) : 0≤C := (h.charge (p:=0) (Work.F07.realStrip _ he (by simp))).credit
lemma mono (h : Ledger X Y F σ C) (hv : D≤σ) (ht : C≤B) : Ledger X Y F D B := ⟨fun {p} w => (h.charge (fun i => (w i).trans_le hv)).mono ht,
    fun i p q w => (h.feat i (w.part hv)).mono ht,fun i j p q r w => (h.dues i j (w.costs hv)).mono ht⟩
lemma boost (h : Ledger X Y F σ C) (v : ℂ) : Ledger X Y (F.weight v) σ (‖v‖*C) := ⟨fun {p} w => (h.charge w).billed v,fun i p q w => (h.feat i w).billed v,fun i j p q r w => (h.dues i j w).billed v⟩
lemma plus (h : Ledger X Y F σ C) (hp : Ledger X Y L σ D) : Ledger X Y (F.plus L) σ (C+D) := ⟨fun {p} w => (h.charge w).plus (hp.charge w), fun i p q w => (h.feat i w).plus (hp.feat i w),fun i j p q r w => (h.dues i j w).plus (hp.dues i j w)⟩
lemma twirls (h : Ledger X Y F σ C) : Ledger Y.dual X.dual F.rear σ C := by
  refine ⟨fun {p} w => ?_, fun i p q w => ?_,fun i j p q r w => ?_⟩
  · simpa only [neg_neg,Film.rear] using (h.charge (negResident w)).slide
  · have he := (h.feat i w.late).slide; rw [neg_neg,show -(-(q+p)+p)=q by abel] at he; exact he
  have he := (h.dues i j w.ebb).slide; rw [neg_neg,show -(-(r+(p+q))+(p+q))=r by abel] at he; exact he
lemma freight (h : Ledger X Y F σ C) (p : Charges Y Z G σ B) (he : 0<σ) : Ledger X Z (F.pay G) σ (4*C*B) := by
  have hc := h.credit he; have hb := p.funds he
  refine ⟨fun {q} w => ((h.charge w).pay (p.base w)).mono (by nlinarith), fun i q t w => ?_,fun i j q t r w => ?_⟩
  · exact (((h.feat i w).pay (p.base w.basic)).plus ((h.charge w.added).pay (p.detail i w))).mono (by nlinarith)
  have h1 := (h.feat j w.roads).pay (p.detail i w.oneWay)
  have h2 := (h.feat i w.proceed).pay (p.detail j w.second)
  rw [add_assoc] at h1; rw [add_right_comm,add_assoc] at h2
  exact (((((h.dues i j w).pay (p.base w.oneWay.basic)).plus h1).plus h2).plus ((h.charge w.total).pay (p.stamp i j w))).mono (by linarith)
lemma freights (h : Ledger Y Z G σ D) (p : Charges X Y F σ C) (he : 0<σ) : Ledger X Z (F.pay G) σ (4*C*D) := by
  have hc := p.funds he; have hb := h.credit he
  refine ⟨fun {q} w => ((h.charge w).taken (p.base w)).mono (by nlinarith), fun i q t w => ?_,fun i j q t r w => ?_⟩
  · exact (((h.charge w.basic).taken (p.detail i w)).plus ((h.feat i w).taken (p.base w.added))).mono (by nlinarith)
  have h1 := (h.feat i w.oneWay).taken (p.detail j w.roads)
  have h2 := (h.feat j w.second).taken (p.detail i w.proceed)
  rw [add_assoc] at h1; rw [add_right_comm,add_assoc] at h2
  exact (((((h.charge w.oneWay.basic).taken (p.stamp i j w)).plus h1).plus h2).plus ((h.dues i j w).taken (p.base w.total))).mono (by linarith)
lemma origin (h : Charges X Y F σ C) : Ledger X Y F σ ((Fintype.card α:ℝ)*C) := ⟨fun {p} w => bags.crew (h.base w), fun i p q w => bags.crew (h.detail i w),fun i j p q r w => bags.crew (h.stamp i j w)⟩

-- move indices
lemma advance (h : Ledger X Y F σ C) {T : Slab β} (ht : ∀ p ∈ strip σ,serial Y T p p 1 D) : Ledger X T F σ (C*D) := by
  refine ⟨fun {p} w => ?_, fun i p q w => ?_, fun i j p q r w => ?_⟩
  · simpa using (h.charge w).pay (ht p w)
  · simpa using (h.feat i w).pay (ht _ w.basic)
  simpa using (h.dues i j w).pay (ht _ w.oneWay.basic)
lemma factors (h : Ledger X Y F σ C) {T : Slab α} (ht : ∀ p ∈ strip σ,serial T X p p 1 D) : Ledger T Y F σ (D*C) := by
  refine ⟨fun {p} w => ?_, fun i p q w => ?_, fun i j p q r w => ?_⟩
  · simpa using (h.charge w).taken (ht p w)
  · simpa using (h.feat i w).taken (ht _ w.added)
  simpa using (h.dues i j w).taken (ht _ w.total)
end Ledger

lemma triple_charge {U : Film ι α α} {X : Slab α} (h : Charges X X U σ C) (he : ∀ p∈strip σ,bags X X p p (U.tab p) D) (hs : 0<σ) : Ledger X X (tripleFilm U) σ (20*C*C*D) := by
  have hc := h.funds hs; have hd := (he (0:Momentum) (Work.F07.realStrip _ hs (by simp))).credit
  let F := U.pay U
  have hF : Charges X X F σ _ := h.pay h hs
  have H1 p (hz : p∈strip σ) : bags X X p p (F.tab p) (C*D) := (he p hz).taken (h.base hz)
  have H2 i p q (hv : Avenue σ p q) : bags X X (q+p) q (F.spot i p q) (2*C*D) := by
    exact (((he q hv.basic).taken (h.detail i hv)).plus ((he _ hv.added).pay (h.detail i hv))).mono (by linarith)
  have hx : 0≤C*C*D := mul_nonneg (mul_nonneg hc hc) hd
  refine ⟨fun {p} w => ((he p w).taken (hF.base w)).mono (by linarith),fun i p q w => ?_, fun i j p q r w => ?_⟩
  · exact (((he q w.basic).taken (hF.detail i w)).plus ((H1 _ w.added).pay (h.detail i w))).mono (by linarith)
  have h1 := (H2 j _ _ w.roads).pay (h.detail i w.oneWay)
  have h2 := (H2 i _ _ w.proceed).pay (h.detail j w.second)
  rw [add_assoc] at h1; rw [add_right_comm,add_assoc] at h2
  exact (((((he r w.oneWay.basic).taken (hF.stamp i j w)).plus h1).plus h2).plus ((H1 _ w.total).pay (h.stamp i j w))).mono (by linarith)
end YM.Stationary
end

/-!
# Pre-L tariffs for Ω/R1 & thin sectors. `parcels` valid at width
paid by soda_cube; invite inputs explicit σ.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι] {G : Gauge} {L : Side} {P : Patch} {C A B D τ σ : ℝ} {p q : Momentum}

-- twice reweights
lemma advancing (h : σ≤1) {M : Film ι (Co L α) (Co L α)} (hp : Charges (Slab.basic _) (Slab.basic _) M σ (inch L^2*C)) : Charges (altarTile L α|>.dual) (altarTile L α) M σ (Real.exp 4*C*Real.exp 4) := by
  convert advance (revertX hp (westward h)) (leftward h) using 1
  field_simp [(inch_pos L).ne']
lemma regaling (h : σ≤1) {M : Film ι (Co L α) (Co L α)} (hp : Ledger (Slab.basic _) (Slab.basic _) M σ (inch L^2*C)) : Ledger (altarTile L α|>.dual) (altarTile L α) M σ (Real.exp 4*C*Real.exp 4) := by
  convert Ledger.advance (Ledger.factors hp (westward h)) (leftward h) using 1
  field_simp [(inch_pos L).ne']
lemma shining (h : σ≤1) {M : Film ι (Co L α) (Co L α)} (hp : Charges (altarTile L α) (altarTile L α|>.dual) M σ (inch L^2*C)) : Charges (Slab.basic _) (Slab.basic _) M σ (Real.exp 4*C*Real.exp 4) := by
  convert advance (revertX hp (leftward h)) (westward h) using 1
  field_simp [(inch_pos L).ne']

-- uniform bubbles require σ≤1/128 theorem param. `AmoMeter` cost independent volume implicit.
def tonPay (G : Gauge) (j : ℕ) (C : ℝ) := 4*paceTariff G j C * paceTariff G j C
def amoPay (G : Gauge) (j : ℕ) (C : ℝ) := tonPay G j C + Real.exp 4*Real.exp 4
def icePay (a b : ℝ) := a+a*b*a+(a*b*a*b+a*b*a*b+a*b)*a

def mealPeb (G : Gauge) (j : ℕ) (C D : ℝ) := Real.exp 4*icePay D (amoPay G j C)*Real.exp 4
def thirds (F : ℝ) := 4*(4*F*F)*F
def mealTr (G : Gauge) (j : ℕ) (C D : ℝ) := thirds (mealPeb G j C D)
def mealCa (G : Gauge) (j : ℕ) (C D : ℝ) := thirds (mealTr G j C D)
def bookTr (G : Gauge) (j : ℕ) (C D : ℝ) := let p := mealTr G j C D; let q := (Real.exp (1/128*4)*((Fintype.card (Loc G 0):ℝ)*(8*jointMoney)))*Real.exp (1/128*4); 20*p*p*q

def Amateur (G : Gauge) (L : Side) (σ D : ℝ) := Freezer (altarTile L (Loc G 0)|>.dual) (altarTile L _) (furnish L (fun p => soda (inch L) p • (1:CompM (Loc G 0) (Loc G 0)))) σ D
lemma amasses (G : Gauge) : ∃ (η a : ℝ),0<η∧η≤1/128 ∧ 0≤a ∧ ∀ L : Side, ∀ σ≤η, Amateur G L σ a := by
  obtain ⟨η,b,h,he,hk,hf⟩ := ammo_bill G; exact ⟨η,b,h,he,hk,fun L _ hw => (hf L).mono hw le_rfl⟩
variable {E : Eye ι (Acts G P)}
lemma amid (hp : Amateur G P.L σ D) : Freezer (altarTile P.L (Loc G 0)|>.dual) (altarTile P.L _) (amFilm E).tab σ D := Freezer.passes hp (fun i hi => (amc_ground E hi).symm)




lemma tonic_points (h : Spotlight P E σ C) (hp : 0<σ) : Charges (altarTile P.L (Loc G 0)|>.dual) (altarTile P.L _) (tonFilm E) σ (tonPay G P.J C) := by
  obtain ⟨hh,H⟩ := paceTariff_pays h hp
  have he := hh.rear; rw [slide_basic] at he; exact he.pay hh hp
lemma ammo_points (h : Spotlight P E σ C) (hp : 0<σ) : Charges (altarTile P.L (Loc G 0)|>.dual) (altarTile P.L _) (amFilm E) σ (amoPay G P.J C) := by
  let μ := inch P.L
  let K := Film.cardF (ι:=ι) (fun _ : Momentum => μ^2 • (1:CompM (Co P.L (Loc G 0)) (Co P.L (Loc G 0))))
  have hx : Charges (Slab.basic _) (Slab.basic _) K σ (μ^2*1) := by
    refine Charges.current (Poster.web _) (by positivity) fun i _ => ?_
    have ht := serial.costs (X:=Slab.basic (Co P.L (Loc G 0))) (p:=i) (q:=i) serial.free (a:= ((μ^2:ℝ):ℂ)); simp only [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)] at ht; exact ht
  have hp := advancing h.width hx; rw [mul_one (Real.exp 4)] at hp; exact Charges.plus (tonic_points h ‹0<σ›) hp
lemma pebbles_frozen (h : Spotlight P E σ C) (he : 0<σ) (hp : Amateur G P.L σ D) : Charges (Slab.basic _) (Slab.basic _) (pebFilm E) σ (mealPeb G P.J C D) := by
  have hx := (ammo_points h he)
  have hh := Freezer.back hx (amid hp) he |>.weight (((inch P.L)^2:ℝ):ℂ)
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at hh; exact shining h.width hh
lemma cannon_frozen (h : Spotlight P E σ C) (he : 0<σ) (hp : Amateur G P.L σ D) : Charges (Slab.basic _) (Slab.basic _) (cannonFilm E) σ ((inch P.L)^2*mealCa G P.J C D) := by
  have hx := pebbles_frozen h he hp
  have hh := (triple_act _ (triple_act _ hx he) he).weight (((inch P.L)^2:ℝ):ℂ)
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at hh; exact hh
lemma gran_frozen (h : Spotlight P E σ C) (he : 0<σ) (hp : Amateur G P.L σ D) : Charges (altarTile P.L (Loc G 0)|>.dual) (altarTile P.L _) (grenadeFilm E) σ (tonPay G P.J C+Real.exp 4*mealCa G P.J C D*Real.exp 4) := Charges.plus (tonic_points h he) (advancing h.width (cannon_frozen h he hp))
lemma fuelCredit (h : Spotlight P E σ C) (he : 0<σ) (hp : Amateur G P.L σ D) (hs : σ≤1/128) : Ledger (Slab.basic _) (Slab.basic _) (cannonFilm E) σ ((inch P.L)^2*bookTr G P.J C D) := by
  have hx := triple_act _ (pebbles_frozen h he hp) he
  have hf i (hi : i∈strip σ) : bags (Slab.basic _) (Slab.basic _) i i ((tripleFilm (pebFilm E)).tab i) ((Real.exp (1/128*4)*((Fintype.card (Loc G 0):ℝ)*(8*jointMoney)))*Real.exp (1/128*4)) := by
    have hh : i∈strip (1/128:ℝ) := fun j => (hi j).trans_le hs; rw [peb_triple E hh]; exact thin_doubled _ P.odd_side hh
  have hh := (triple_charge hx hf he).boost (((inch P.L)^2:ℝ):ℂ); rw [Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)] at hh; exact hh
end YM.Stationary
end
