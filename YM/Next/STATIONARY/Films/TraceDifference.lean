import YM.Next.STATIONARY.Films.ThinTrace
import YM.Work.A04

set_option autoImplicit false
/-!
# Some Film algebra over columns. Always acts at these width hats.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ] [Fintype ι] [DecidableEq ι] {C D σ : ℝ} {F : Film ι α β}

namespace Film
lemma compare {X Y : Film ι α β} (ht : ∀ p,X.tab p=Y.tab p) (hv : ∀ i p q,X.spot i p q=Y.spot i p q) (hp : ∀ i j p q r,X.arch i j p q r=Y.arch i j p q r) : X=Y := by
  have he : X.tab=Y.tab := funext ht
  have hx : X.spot=Y.spot := funext (fun i => funext (fun p => funext (hv i p)))
  have h := funext (fun i => funext (fun j => funext (fun p => funext (fun q => funext (hp i j p q)))))
  cases X; cases Y; congr
lemma distL (X Y : Film ι α β) (T : Film ι β γ) : (X.plus Y).pay T=(X.pay T).plus (Y.pay T) := by
  apply compare
  · intro p; simp only [Film.pay,Film.plus,Pi.add_apply, Matrix.add_mul]
  · intro i p q; simp only [Film.pay,Film.plus,Pi.add_apply, Matrix.add_mul]; abel
  intro i j p q r; simp only [Film.pay,Film.plus,Pi.add_apply, Matrix.add_mul]; abel
lemma distR (X : Film ι α β) (Y T : Film ι β γ) : X.pay (Y.plus T)=(X.pay Y).plus (X.pay T) := by
  apply compare
  · intro p; simp only [Film.pay,Film.plus,Pi.add_apply, Matrix.mul_add]
  · intro i p q; simp only [Film.pay,Film.plus,Pi.add_apply, Matrix.mul_add]; abel
  intro i j p q r; simp only [Film.pay,Film.plus,Pi.add_apply, Matrix.mul_add]; abel
lemma combining (X : Film ι α β) (Y : Film ι β γ) (Z : Film ι γ δ) : (X.pay Y).pay Z=X.pay (Y.pay Z) := by
  apply compare
  · intro p; simp only [Film.pay, Matrix.mul_assoc]
  · intro i p q; simp only [Film.pay,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]; abel
  intro i j p q r; simp only [Film.pay,Matrix.mul_add,Matrix.add_mul,Matrix.mul_assoc]; rw [add_right_comm r q p]; simp only [add_assoc r]; abel
lemma rear_dist (X : Film ι α β) (Y : Film ι β γ) : (X.pay Y).rear= Y.rear.pay X.rear := by
  apply compare
  · intro p; simp only [Film.pay,Film.rear,Matrix.transpose_mul]
  · intro i p q; simp only [Film.pay,Film.rear,Matrix.transpose_add,Matrix.transpose_mul]; rw [show -(q+p)+p= -q by abel]; abel
  intro i j p q r; simp only [Film.pay,Film.rear,Matrix.transpose_add,Matrix.transpose_mul]
  rw [add_right_comm r q p, add_assoc r]
  rw [show -(r+(p+q))+p= -(r+q) by abel,show -(r+(p+q))+q= -(r+p) by abel,show -(r+(p+q))+(p+q) = -r by abel]; abel
lemma rear_plus (X Y : Film ι α β) : (X.plus Y).rear=X.rear.plus Y.rear := compare (fun _ => Matrix.transpose_add ..) (fun _ _ _=> Matrix.transpose_add ..) (fun _ _ _ _ _=> Matrix.transpose_add ..)
lemma reverseF (X : Film ι α β) : X.rear.rear=X := by
  apply compare
  · intro p; simp only [Film.rear, Matrix.transpose_transpose,neg_neg]
  · intro i p q; simp only [Film.rear, Matrix.transpose_transpose]; rw [show -(-(q+p)+p)=q by abel]
  intro i j p q r; simp only [Film.rear, Matrix.transpose_transpose]; rw [show -(-(r+(p+q))+(p+q))=r by abel]
end Film

-- Axis sum, append Proof. avoid TC Add instance on Movie.

def chore (l : List γ) (F : γ→Film ι α β) : Film ι α β := match l with
    | [] => Film.cardF 0
    | i::l => (F i).plus (chore l F)
lemma chorePay {F : γ→Film ι α β} (p : List γ) (k : γ→ℝ) {X : Slab α} {Y : Slab β} (h : ∀ i∈p, Charges X Y (F i) σ (k i)) : Charges X Y (chore p F) σ (p.map k).sum := by
  induction p with
  | nil => exact Charges.current (Poster.web _) le_rfl (fun i _ => serial.flat)
  | cons a l ih => exact (h a (List.mem_cons_self)).plus (ih (fun i hi => h i (by simp [hi])))
lemma choreGift {F : γ→ Film ι α β} (p : List γ) (k : γ→ℝ) {X : Slab α} {Y : Slab β} (h : ∀ i ∈p, Ledger X Y (F i) σ (k i)) : Ledger X Y (chore p F) σ (p.map k).sum := by
  induction p with
  | nil => exact ⟨fun _=> bags.zero le_rfl,fun _ _ _ _=> bags.zero le_rfl,fun _ _ _ _ _ _ => bags.zero le_rfl⟩
  | cons a l ih => exact (h a (List.mem_cons_self)).plus (ih (fun i hi => h i (by simp [hi])))
lemma choreL {F : γ→Film ι α β} (p : List γ) (h : ∀ i∈p, Play (F i) σ) : Play (chore p F) σ := by
  induction p with
  | nil => exact Play.current (Poster.web _)
  | cons a l ih => exact (h _ List.mem_cons_self).plus (ih (fun i hi => h i (by simp [hi])))
lemma tipScale (p : List γ) (k : γ→ℝ) (c : ℝ) : (p.map (fun i=> c*k i)).sum=c*(p.map k).sum := by
  induction p with
  | nil => simp
  | cons a l ih => simp [ih,mul_add]
lemma choreRuns {F : γ→Film ι α β} (p : List γ) {m : Side} {U : γ→ OperatorF ι m α β} (h : ∀ i∈p,Ticket (F i) (U i)) : Ticket (chore p F) ((p.map U).sum) := by
  induction p with
  | nil =>
    apply Ticket.current (U:=0); rw [show approached (0:Matrix (Co m α) (Co m β) ℝ)=0 by ext; simp [approached]]; exact Jaunt.zero _
  | cons a l ih => exact (h _ List.mem_cons_self).plus (ih (fun i hi => h i (by simp [hi])))
end YM.Stationary
end

/-!
# Stack montage of reference and station determinants. Κ fields at same
exponential jet convention. Mission arc includes Mass determinant Δ; no
fixed-post pricing transferred to the absolute L budgets via these
identities. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {p : Clip} {R : PathData G} {σ A C D : ℝ} {c f L : Side}
section sea
variable (G)
def buttF (G : Gauge) (L : Side) (ι : Type) := Film.cardF (ι:=ι) (fun _ => shardX (Co L (Loc G 1)) (Loc G 0) ℂ)
def brimF (G : Gauge) (L : Side) (ι : Type) := Film.cardF (ι:=ι) (fun _ => shardY (Co L (Loc G 1)) (Loc G 0) ℂ)
def stageFilm (i : Axis) (L : Side) := Film.cardF (ι:=ι) (stairRow G L i)

end sea

section movie
variable (D : Eye ι (Acts G P)) (r : Bool)
abbrev Spark (ι : Type) (G : Gauge) (P : Patch) := Film ι (VRange G 1 P.L) (VRange G 1 P.L)
variable (K : Spark ι G P) (k : ℝ)

def shearGram := (sectorMail P D).rear.pay (buttF G P.L ι)
def emitter := (cannonFilm D).pay (Chromatic r D)
def CanonR := (shearGram D).plus (emitter D r)

def militiaF := (CanonR D r).rear.pay (CanonR D r)
def motiveFilm (P : Patch) (G : Gauge) (i : Type) := (brimF G P.L i).rear.pay (brimF G P.L i)
def motiveRoll (i : Axis) := ((stageFilm (ι:=ι) G i P.L).rear.pay (cannonFilm D)).pay (stageFilm G i P.L)
def chorusRoll := chore (List.finRange 4) (motiveRoll D)
def rankF := (K.plus ((sectorMail P D).pay (sectorMail P D).rear)).plus (chorusRoll D)
def rankUpF := (((buttF G P.L ι).rear.pay (rankF D K)).pay (buttF G P.L ι)).plus (motiveFilm P G ι)

def houseF := ((CharterR r D).rear.pay (CoastF r k D)).pay (CharterR r D)
def legionF := ((((buttF G P.L ι).rear.pay K).pay (buttF G P.L ι)).plus (houseF D r k)).plus (militiaF D r)
def medalF := ((((buttF G P.L ι).rear.pay K).pay (buttF G P.L ι)).plus (BoomF r k D)).plus (militiaF D r)

end movie
section bills
variable (G) (S : StepData c f)
def rankUp (p : Clip) (R : PathData G) (U : Config G f) := (butt G c f)ᵀ* rankAux U p R (inch S.patch.L)* butt _ _ _ + (brim G c f)ᵀ *brim G c f
-- Real determinant surgery between rankUp and rankAux later.
lemma buttRoad : Ticket (buttF G S.patch.L ι) (fun _ : Corn (Co c ι) => repackM (unitSplit G S 1) (clothe _ S) (butt G c f)) := by classical exact Ticket.current _ _ butt_travel
lemma brimRoad : Ticket (brimF G S.patch.L ι) (fun _ : Corn (Co c ι) => repackM (Equiv.refl _) (clothe _ S) (brim G c f)) := by classical exact Ticket.current _ _ brim_travel
variable {G S}
end bills
section dialogs
variable (S : StepData c f) (t : S.Choices) (r : Bool) (Z : Corn (Co c ι) →L[ℝ] Bang G c f)
    {D : Eye ι (Acts G S.patch)} {K : Spark ι G S.patch} {R : PathData G} {p : Clip}
    (h : Turns D (billZ S Z)) (hp : S.patch.Branches S.kernel G)
    (hq : ∀ x,(Z x).2.1=0) (hr : ∀ x,(Z x).2.2=0) (he : Ticket K (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (flare p R (headingF S t r Z x))))
include h
lemma chore_lifts : Ticket (chorusRoll D) (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (brigadeM (cannon (inch S.patch.L) (headingF S t r Z x)))) := by
  classical
  let X : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0; let Y : Lines G f 1≃ Co c (Co S.patch.L (Loc G 1)) := unitSplit G S 1
  let F x := cannon (inch S.patch.L) (headingF S t r Z x)
  let V := fun i x => repackM Y Y ((stagehand i G f)ᵀ*F x * stagehand i G f)
  let p := List.finRange 4
  have hx i : Ticket (stageFilm G i S.patch.L (ι:=ι)) (fun _ : Corn (Co c ι) => repackM X Y (stagehand i G f)) := Ticket.current _ _ (seatOpen G S i)
  have hv i : Ticket (motiveRoll D i) (V i) := by
    refine Ticket.foreign (((hx i).rear.pay (fuel_reel S t r Z h)).pay (hx i)) ?_
    filter_upwards with x; unfold V; rw [repack_multiply _ X, repack_multiply _ X, repack_rotate]; rfl
  refine (choreRuns p (U:=V) (fun i _ => hv i)).foreign ?_
  refine Eventually.of_forall fun x => ?_
  rw [show (p.map V).sum=∑ i,V i from ?_]
  · rw [Finset.sum_apply]; change ∑ i,V i x=repackM Y Y (brigadeM (F x)); ext i j; simp [V,brigadeM,repackM,Matrix.sum_apply]
  rw [← Fin.sum_univ_def]
include he
lemma rank_lyrics : Ticket (rankF D K) (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (rankAux (headingF S t r Z x) p R (inch S.patch.L))) := by
  classical
  have hz := mail_for S Z h t r
  apply Ticket.foreign ((he.plus (hz.pay hz.rear)).plus (chore_lifts S t r Z h)); filter_upwards with x
  let i : Lines G f 1≃ Co c (Co S.patch.L (Loc G 1)) := unitSplit G S 1; let j : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  let U := headingF S t r Z x
  let F := flare p R U; let V := mail U; let T := brigadeM (cannon (inch S.patch.L) U)
  change _=repackM i i (F+ V*Vᵀ +T)
  rw [show repackM i i _=repackM i i F+repackM i i (V*Vᵀ)+repackM i i T from rfl,repack_multiply _ j,repack_rotate]; rfl
lemma rank_up_ticket : Ticket (rankUpF D K) (fun x => repackM (clothe _ S) (clothe G S) (rankUp G S p R (headingF S t r Z x))) := by
  classical
  let F := buttRoad (ι:=ι) G S; let T := brimRoad (ι:=ι) G S
  apply Ticket.foreign (((F.rear.pay (rank_lyrics S t r Z h he)).pay F).plus (T.rear.pay T)); filter_upwards with x
  let U := (butt G c f)ᵀ * rankAux (headingF S t r Z x) p R (inch S.patch.L)*butt G c f; let V := (brim G c f)ᵀ*brim G c f; let e := clothe G S
  change _=repackM e e (U+V); rw [show repackM e e (U+V)=repackM e e U + repackM e e V from rfl]; unfold U V
  rw [repack_multiply _ (unitSplit G S 1),repack_multiply _ (unitSplit G S 1), repack_multiply _ (Equiv.refl _),repack_rotate,repack_rotate]; rfl
include hp hq
omit he in
lemma regulator_tour : Ticket (CanonR D r) (fun x => repackM (unitSplit G S 0) (clothe G S) (cannonade S t (inch S.patch.L) (buffOn S t G r) (headOn S t r (Z x)))) := by
  classical
  have hx := (mail_for S Z h t r).rear.pay (buttRoad (ι:=ι) G S)
  have ht := (fuel_reel S t r Z h).pay (estate S t r hp Z hq h)
  refine Ticket.foreign (hx.plus ht) ?_; filter_upwards with x
  let i : Lines G f 1≃ Co c (Co S.patch.L (Loc G 1)) := unitSplit G S 1; let j : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0; let k := clothe G S
  let U := headingF S t r Z x; let V := indexX S t (buffOn S t G r) (headOn S t r (Z x))
  let M := (mail U)ᵀ * rearM G c f; let T := cannon (inch S.patch.L) U* V
  change _=repackM j k (M+T)
  rw [show repackM j k _=repackM j k M+repackM j k T from rfl]; unfold M T; rw [repack_multiply _ i,repack_multiply _ j (u:=k),repack_rotate]; rfl
omit he in
lemma militia_ride : Ticket (militiaF D r) (fun x => repackM (clothe G S) (clothe G S) (militia S t (inch S.patch.L) (buffOn S t G r) (headOn S t r (Z x)))) := by
  classical
  have hF := regulator_tour S t r Z h hp hq
  refine Ticket.foreign (hF.rear.pay hF) ?_; filter_upwards with x; unfold militia; rw [repack_multiply _ (unitSplit G S 0),repack_rotate]; rfl
include hr
lemma legislature : Ticket (legionF D r K S.kernel.penalty) (fun x => repackM (clothe G S) (clothe G S) (legion S t p R (inch S.patch.L) (buffOn S t G r) (input G c (Z x).1.1) (headOn S t r (Z x)))) := by
  classical
  have hF := issued_one S t r hp Z hq h
  have hp' := coastGift S Z hp t r hq h hr
  let T := ((hF.rear.pay hp').pay hF)
  let V := buttRoad (ι:=ι) G S
  refine Ticket.foreign ((((V.rear.pay he).pay V).plus T).plus (militia_ride S t r Z h hp hq)) ?_; filter_upwards with x
  let i := unitSplit G S 1; let k := clothe G S; let d := Equiv.refl (Lines G c 1)
  let U := headOn S t r (Z x); let P := input G c (Z x).1.1; let W := buffOn S t G r; let c' := inch S.patch.L
  let F := rearM G c f; let M := motions S Z t r x; let H := quota S t W U; let A := militia S t c' W U; let N := flare p R U.1
  change _=repackM k k (Fᵀ*N*F+ Hᵀ*M*H + A)
  rw [show repackM k k _=repackM k k (Fᵀ*N*F) + repackM k k (Hᵀ*M*H)+repackM k k A from rfl, repack_multiply _ i (V:=F),repack_multiply _ i (V:=N),repack_multiply _ d (V:=H),repack_multiply _ d (V:=M), repack_rotate, repack_rotate]; rfl

end dialogs
end YM.Stationary
end

/-!
# Union at N. Vertical classical score includes boom term. Root-frame
may be used qualitatively. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {p : Clip} {R : PathData G} {σ A C D τ Ω Λ : ℝ} {c f L : Side}
section root
variable (S : StepData c f) (hp : S.patch.Branches S.kernel G) (t : S.Choices) (r : Bool)
    (Z : Corn (Co c ι)→L[ℝ] Bang G c f) {D : Eye ι (Acts G S.patch)}
include hp
lemma cloak_open : Thaw (fun x => headOn S t r (Z x)) 0 := by
  have ht : Thaw (fun x => Stationary.extend (Z x).1.2) 0 := Thaw.through (Z.contDiff.contDiffAt.fst.snd)
  cases r
  · exact ht
  exact sport_thaw (fedora_style hp t) ht (by simp [Stationary.extend])
lemma zero_hat : headOn S t r (Z 0)=1 := by
  rw [map_zero]; cases r
  · exact extend_zero
  exact (congr_arg (dress _) extend_zero).trans (dressed_one (fedora_style hp t))
lemma shellCost : Customs (buffOn S t G r) := by cases r; exact fedora_style hp t; exact root_customs

lemma arc_rata (p : Clip) (R : PathData G) (hu : R.Bounds p τ Ω Λ) :
    ∀ᶠ x in 𝓝 0, let U := headOn S t r (Z x); let V := input G c (Z x).1.1
                  let F := buffOn S t G r
                  damage (helmets G c f) (burnJoint S t p R F V U) 0=
                    (rearM G c f)ᵀ*flare p R U.1 * rearM G c f + honorsBox S Z t r x := by
  have he := awake t hu (cloak_open S hp t r Z) (by rw [zero_hat _ hp]; rfl) hp (shellCost S hp t r)
  filter_upwards [he] with x hx
  intro U V F
  let K := burn p R U.1
  let H := fun y => tickets S V (ribbon S t (atire F U y))
  let T := ContinuousLinearMap.fst ℝ (Link G f) (BaseSites G c)
  have hK : ContDiffAt ℝ ω K (T 0) := map_zero T ▸ hx.known
  have hp : ContDiffAt ℝ ω H 0 := by
    unfold H tickets; apply ContDiffAt.mul contDiffAt_const; apply ContDiffAt.sum; intro i _; exact matrix_price_jet (contDiffAt_const.mul (hx.thorn.inv i))
  let B := helmets G c f
  have hv : burnJoint S t p R F V U=(K∘T)+H := rfl
  refine damage_eq B ?_; intro a b; rw [detracts,add_mulVec,dotProduct_add,both_cost,rear_cost,rear_cost]; rw [show dotProduct (cash B a) (honorsBox S Z t r x*ᵥ cash B b)= _ from detracts B H 0 a b, hv,iteratedFDeriv_add_apply ((hK.comp _ T.contDiff.contDiffAt).of_le le_top) (hp.of_le le_top),_root_.add_apply,wired T hK.analyticAt, map_zero]
  have he := detracts (pocket _) K 0 a.1 b.1; rw [cash_pocket,cash_pocket] at he
  rw [show T ∘ ![a,b]=![a.1,b.1] by ext1 i; fin_cases i <;> rfl]; exact congr_arg (·+_) he.symm

lemma rewarded {p : Clip} {R : PathData G} (hu : R.Bounds p τ Ω Λ) (hz : ∀ x,(Z x).2.1=0) (d : Turns D (billZ S Z)) {K : Spark ι G S.patch}
    (he : Ticket K (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (flare p R (headingF S t r Z x)))) : Ticket (medalF D r K S.kernel.penalty) (fun x => repackM (clothe G S) (clothe G S) (medals S t p R (inch S.patch.L) (buffOn S t G r) (input G c (Z x).1.1) (headOn S t r (Z x)))) := by
  classical
  let V := buttRoad (ι:=ι) G S
  refine ((((V.rear.pay he).pay V).plus (honorsGift S Z hp t r hz d)).plus (militia_ride S t r Z d hp hz)).foreign ?_
  filter_upwards [arc_rata S hp t r Z p R hu] with x hx
  dsimp only at hx
  unfold medals; rw [hx]; let U := rearM G c f; let T := flare p R (headingF S t r Z x)
  let X := honorsBox S Z t r x; let Y := militia S t (inch S.patch.L) (buffOn S t G r) (headOn S t r (Z x)); let e := clothe G S
  change _=repackM e e (Uᵀ*T*U+X+Y)
  rw [show repackM e e _=repackM e e (Uᵀ*T*U)+repackM e e X+repackM e e Y from rfl,repack_multiply _ (unitSplit G S 1) (V:=U),repack_multiply _ (unitSplit G S 1) (V:=T),repack_rotate]; rfl
end root
end YM.Stationary
end

/-!
# Montage charge pipeline, vertical context. Standing Gloss from readers,
unit path ext. Reference waves still require κ Spect. `shades_g` root
qualitative with supplied widths (owns no C!). -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {σ A C D τ Ω Λ : ℝ} {k j m : ℕ} {r : Bool}

-- Price chain.
def boots2 (G : Gauge) (j : ℕ) (C D : ℝ) := 4*mealCa G j C D*feeHead (fun k => hatchRate G j k C)
def tribute2 (G : Gauge) (j : ℕ) (C D : ℝ) := 4* paceTariff G j C + boots2 G j C D
def stageDue (G : Gauge) (j : ℕ) (c : ℝ) := feeHead (fun k => lantern G j k c)
def sensor (G : Gauge) (j : ℕ) (c k : ℝ) := let a := stageDue G j c; 4 * (4*a*feeHead (theaterH (fun n => cashDamage G j n (muralRoom j*c) k))) * a
def legPay (G : Gauge) (j : ℕ) (C D k A : ℝ) := 4*(4*A)+sensor G j C k+ (4*tribute2 G j C D* tribute2 G j C D)
def boomPay (G : Gauge) (j : ℕ) (C D k A : ℝ) := 4*(4*A)+ feeHead (theaterH (fun n => cashBook G j n (muralRoom j*C) k))+(4*tribute2 G j C D*tribute2 G j C D)
def seats (G : Gauge) (a : ℝ) := ((List.finRange 4).map fun i => 4*(4*stageTariff G i*a)*stageTariff G i).sum
def uphill (G : Gauge) (j : ℕ) (C D A : ℝ) := A+tonPay G j C+Real.exp 4*seats G (mealCa G j C D)*Real.exp 4
def statusP (G : Gauge) (j : ℕ) (C D A : ℝ) := 4*(4*uphill G j C D A)+4

def Keels (K : Spark ι G P) (σ C : ℝ) := Charges (altarTile P.L (Loc G 1)|>.dual) (altarTile P.L _) K σ C

lemma bursar (G : Gauge) (L : Side) (ι : Type) : Charges (altarTile L (Loc G 1)) (slabW G L) (buttF G L ι) σ 1 := Charges.current (Poster.web _) zero_le_one (fun _ _ => serial_butt ..)
lemma bursar_prism (G : Gauge) (L : Side) (ι : Type) : Charges (Slab.basic (Loc G 0)) (slabW G L) (brimF G L ι) σ 1 := Charges.current (Poster.web _) zero_le_one (fun _ _ => serial_brim ..)
lemma stagepay {L : Side} (i : Axis) (h : σ ≤ 1) : Charges (Slab.basic _) (Slab.basic _) (stageFilm (ι:=ι) G i L) σ (stageTariff G i) := by
  refine Charges.current (rowNice i) (by unfold stageTariff; positivity [flux_nonneg (dasher G i)]) fun p he => ?_
  exact plankPrice (fun _ => dasher G i) (fun i => (he i).trans_le h) (flux_nonneg _) (fun _=> le_rfl)
section paid
variable {K : KernelChoices} (hp : P.Branches K G) (hs : 0<σ) {E : Eye ι (Acts G P)} (h : Spotlight P E σ C) (hF : Amateur G P.L σ D)
include h hs
lemma shearPaid : Charges (Slab.basic _) (slabW G P.L) (shearGram E) σ (4*paceTariff G P.J C) := by
  have hx := (paceTariff_pays h hs).2.rear; rw [Slab.retro,slide_basic] at hx
  simpa only [mul_one,shearGram] using hx.pay (bursar G P.L ι) hs
lemma prism_pay2 : Charges (slabW G P.L|>.dual) (slabW G P.L) (motiveFilm P G ι) σ 4 := by
  have he := bursar_prism (σ:=σ) G P.L ι; have hy := he.rear; rw [slide_basic] at hy; simpa only [mul_one,motiveFilm] using hy.pay he hs
include hp
lemma homes (k : ℝ) : Charges (slabW G P.L|>.dual) (slabW G P.L) (houseF E false k) σ (sensor G P.J C k) := by
  have hv := CharterR.costs h hp
  have hb := CoastF.costs h hp k
  have hc := hv.rear; rw [slide_basic] at hc
  exact (hc.pay hb hs).pay hv hs
include hF
lemma elevation_pay : Charges (Slab.basic _) (slabW G P.L) (emitter E false) σ (boots2 G P.J C D) := by
  have ht := (cannon_frozen h hs hF).pay (Chromatic.costs h hp) hs
  convert ht using 1 <;> first | rfl | (unfold boots2 inch; field_simp)
lemma conquer : Charges (Slab.basic _) (slabW G P.L) (CanonR E false) σ (tribute2 G P.J C D) := by
  apply Charges.plus (shearPaid hs h) (elevation_pay hp hs h hF)
lemma specialOps : Charges ((slabW G P.L).dual) (slabW G P.L) (militiaF E false) σ (4*tribute2 G P.J C D* tribute2 G P.J C D) := by
  have he := conquer hp hs h hF; have ht := he.rear; rw [slide_basic] at ht; exact ht.pay he hs

lemma legion_right (U : Spark ι G P) (hv : Keels U σ A) : Charges ((slabW G P.L).dual) (slabW G P.L) (legionF E false U K.penalty) σ (legPay G P.J C D K.penalty A) := by
  have hu : _ := bursar (σ:=σ) G P.L ι
  have hx := (hu.rear.pay hv hs).pay hu hs; simp only [mul_one] at hx
  exact (hx.plus (homes hp hs h K.penalty)).plus (specialOps hp hs h hF)
lemma medals_right (U : Spark ι G P) (hv : Keels U σ A) : Charges ((slabW G P.L).dual) (slabW G P.L) (medalF E false U K.penalty) σ (boomPay G P.J C D K.penalty A) := by
  have hu : _ := bursar (σ:=σ) G P.L ι
  have hx := (hu.rear.pay hv hs).pay hu hs; simp only [mul_one] at hx
  exact (hx.plus (BoomF.costs h hp K.penalty)).plus (specialOps hp hs h hF)

omit hp
lemma roll_round : Charges (Slab.basic _) (Slab.basic _) (chorusRoll E) σ ((inch P.L)^2*seats G (mealCa G P.J C D)) := by
  let a := mealCa G P.J C D
  let p := inch P.L^2
  unfold seats; rw [← tipScale]
  refine chorePay _ _ (fun i _ => ?_)
  have hx := stagepay (L:=P.L) (G:=G) (ι:=ι) i h.width; have hv := hx.rear; rw [slide_basic,slide_basic] at hv
  convert (hv.pay (cannon_frozen h hs hF) hs).pay hx hs using 1 <;> first | rfl | ring
lemma rankRight (U : Spark ι G P) (hv : Keels U σ A) : Keels (rankF E U) σ (uphill G P.J C D A) := by
  have ht := (paceTariff_pays h hs).2; have he := ht.rear
  rw [slide_basic, Slab.retro] at he
  exact (Charges.plus hv (ht.pay he hs)).plus (advancing h.width (roll_round hs h hF))
lemma rankUpRight (U : Spark ι G P) (hv : Keels U σ A) : Charges (slabW G P.L|>.dual) (slabW G P.L) (rankUpF E U) σ (statusP G P.J C D A) := by
  have hh := bursar (σ:=σ) G P.L ι
  have ht := (hh.rear.pay (rankRight hs h hF U hv) hs).pay hh hs; simp only [mul_one] at ht
  exact ht.plus (prism_pay2 hs h)
end paid

-- qualitative rooting


end YM.Stationary
end

/-!
# Uniform trace-idealized Hessian difference Θ. Requires CANON r=center for
C only. No costs for shear auxiliary or for Kin at this point. Compare
same E. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {α β γ δ ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {K : KernelChoices} {σ A C D : ℝ}

section eta
variable (E : Eye ι (Acts G P)) (r : Bool) (k : ℝ)

-- compare gram parts: sectorMail + emit; only pure bows cancel rank. Difference of - chorus part & Id.
def isolates (E : Eye ι (Acts G P)) := ((buttF G P.L ι).rear.pay (chorusRoll E)).pay (buttF G P.L ι)
def reflects := (((emitter E r).rear).pay (CanonR E r)).plus ((shearGram E).rear.pay (emitter E r))
def barker := outstanding ((houseF E r k).plus (reflects E r)) ((isolates E).plus (motiveFilm P G ι))
lemma ledger_book (U : Spark ι G P) : outstanding (legionF E r U k) (rankUpF E U)=barker E r k := by
  let X := shearGram E
  let T := emitter E r
  let Y := reflects E r
  let s := buttF G P.L ι
  let t := sectorMail P E
  have hp : militiaF E r=(X.rear.pay X).plus (reflects E r) := by
    change ((X.plus T).rear.pay (X.plus T))= _; rw [Film.rear_plus, Film.distL,Film.distR X.rear]
    change (((X.rear.pay X).plus (X.rear.pay T)).plus (T.rear.pay (X.plus T)))=(X.rear.pay X).plus ((T.rear.pay (X.plus T)).plus (X.rear.pay T));
    apply Film.compare
    · intro p; simp [Film.plus]; abel
    · intro i p q; simp [Film.plus]; abel
    intro i j p q r; simp [Film.plus]; abel
  have he : X.rear.pay X=(s.rear.pay (t.pay t.rear)).pay s := by
    change (t.rear.pay s).rear.pay (t.rear.pay s)= _; rw [Film.rear_dist,Film.reverseF,Film.combining,Film.combining,Film.combining]
  let N := (s.rear.pay U).pay s; let M := X.rear.pay X; let H := houseF E r k
  have hg : rankUpF E U = (((N.plus M).plus (isolates E)).plus (motiveFilm P G ι)) := by unfold rankUpF rankF; simp only [Film.distL, Film.distR]; unfold M; rw [he]; rfl
  rw [hg]; unfold legionF; rw [hp]
  change outstanding ((N.plus H).plus (M.plus Y)) (((N.plus M).plus (isolates E)).plus (motiveFilm P G ι))=outstanding (H.plus Y) ((isolates E).plus (motiveFilm P G ι))
  apply Film.compare
  · intro p; simp [outstanding,Film.plus,Film.weight]; abel
  · intro i p q; simp [outstanding,Film.plus,Film.weight]; abel
  intro i j p q r; simp [outstanding,Film.plus,Film.weight]; abel
end eta

def popLedger (G : Gauge) := 4 * (Fintype.card (Loc G 0):ℝ)

def orbitLedger (G : Gauge) (j : ℕ) (C D : ℝ) := Real.exp 4*seats G (bookTr G j C D)*Real.exp 4
def regLedger (G : Gauge) (j : ℕ) (C D : ℝ) := 4*bookTr G j C D*feeHead (fun k=>hatchRate G j k C)
def reflectLedger (G : Gauge) (j : ℕ) (C D : ℝ) := let a := regLedger G j C D; 4*a* tribute2 G j C D + 4*(4*paceTariff G j C)*a
def payLedger (G : Gauge) (j : ℕ) (C k : ℝ) := let a := stageDue G j C; let b := feeHead (theaterH fun n=> cashDamage G j n (muralRoom j*C) k); 4 * (4 * a * ((Fintype.card (Loc G 1):ℝ)*b))*a
def barkPay (G : Gauge) (j : ℕ) (C D k : ℝ) := (payLedger G j C k+reflectLedger G j C D)+(4*(4*orbitLedger G j C D)+popLedger G)

section prep
variable {E : Eye ι (Acts G P)} (h : Spotlight P E σ C) (hs : 0<σ) (hl : Amateur G P.L σ D) (ht : σ≤1/128) (hp : P.Branches K G)

lemma motive_budget (P : Patch) (hs : 0<σ) : Ledger (slabW G P.L|>.dual) (slabW G P.L) (motiveFilm P G ι) σ (popLedger G) := by
  let T := brimF G P.L ι
  have he : Charges _ _ T σ _ := bursar_prism (σ:=σ) G P.L ι
  have hx := he.rear; rw [slide_basic] at hx
  unfold popLedger; have hh := (Ledger.origin he).freights hx hs; rw [mul_one,mul_one] at hh; exact hh
include h hs hp
lemma house_owed : Ledger (slabW G P.L|>.dual) (slabW G P.L) (houseF E false K.penalty) σ (payLedger G P.J C K.penalty) := by
  have hv := CharterR.costs h hp
  have hb := CoastF.costs h hp K.penalty
  have hc := hv.rear; rw [slide_basic] at hc
  exact ((Ledger.origin hb).freights hc hs).freight hv hs
include hl ht
omit hp in
lemma orbit_owed : Ledger (altarTile P.L (Loc G 1)|>.dual) (altarTile P.L _) (chorusRoll E) σ (orbitLedger G P.J C D) := by
  apply regaling h.width
  unfold seats; rw [← tipScale]
  refine choreGift _ _ (fun i _ => ?_)
  have hx := stagepay (L:=P.L) (G:=G) (ι:=ι) i h.width; have hv := hx.rear; rw [slide_basic,slide_basic] at hv
  convert ((fuelCredit h hs hl ht).freights hv hs).freight hx hs using 1 <;> first | rfl | ring
lemma regionLedger : Ledger (Slab.basic _) (slabW G P.L) (emitter E false) σ (regLedger G P.J C D) := by
  have hF := fuelCredit h hs hl ht; have hi := hF.freight (Chromatic.costs h hp) hs
  convert hi using 1 <;> first | rfl | (unfold regLedger inch; field_simp)
lemma lens_paid : Ledger (slabW G P.L|>.dual) (slabW G P.L) (reflects E false) σ (reflectLedger G P.J C D) := by
  have he := regionLedger h hs hl ht hp
  have hv := he.twirls; rw [slide_basic] at hv
  have hh := (shearPaid hs h).rear; rw [slide_basic] at hh
  exact (hv.freight (conquer hp hs h hl) hs).plus (he.freights hh hs)
lemma full_tolls (U : Spark ι G P) : Ledger (slabW G P.L|>.dual) (slabW G P.L) (outstanding (legionF E false U K.penalty) (rankUpF E U)) σ
    (barkPay G P.J C D K.penalty) := by
  rw [ledger_book]
  have he := bursar (σ:=σ) G P.L ι
  have hm := ((orbit_owed h hs hl ht).freights he.rear hs).freight he hs; rw [mul_one,mul_one] at hm
  apply Ledger.plus ((house_owed h hs hp).plus (lens_paid h hs hl ht hp))
  have hv := (hm.plus (motive_budget P hs)).boost (-1); rw [norm_neg,norm_one,one_mul] at hv; exact hv
end prep
end YM.Stationary
end

/-!
# Auxiliary rank proof escrow and union at commonM arc. Step actual mark,
no constancy hypothesis for inputs over flags in any hs.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {K : KernelChoices} {σ A C D : ℝ} {c f : Side}
section join
lemma matBlocks (R : Type) [CommRing R] (U : Matrix α α R) : (shardX α β R)ᵀ*U*shardX α β R +(shardY α β R)ᵀ*shardY α β R =fromBlocks U 0 0 1 := by
  ext (i|i) (j|j) <;> simp [Matrix.mul_apply,shardX,shardY,LinearMap.toMatrix'_apply,Fintype.sum_sum_type,Pi.single_apply,Matrix.one_apply,ite_mul,mul_ite] <;> simp only [eq_comm]
end join

lemma headquarters (S : StepData c f) (p : Clip) (R : PathData G) (U : Config G f) : (rankUp G S p R U).det=(rankAux U p R (inch S.patch.L)).det := by
  simp only [rankUp,helmet_butt,helmet_brim, matBlocks]; rw [det_fromBlocks_zero₁₂,det_one,mul_one]
lemma rankUpFreeze {E : Eye ι (Acts G P)} {T : Spark ι G P} (hv : Freezer (altarTile _ _ |>.dual) (altarTile _ _) (rankF E T).tab σ A) : Freezer (slabW G P.L|>.dual) (slabW G P.L) (rankUpF E T).tab σ (max A 1) := by
  let Y := rankF E T; let K := rankUpF E T
  have hx p : K.tab p=spades (Y.tab p) 1 := matBlocks ℂ _
  refine ⟨fun p hp => ?_,fun p hp => ?_⟩
  · change IsUnit (K.tab p).det; rw [hx,spades, det_fromBlocks_zero₁₂]; simpa using hv.period p hp
  change serial _ _ p p (K.tab p)⁻¹ _
  rw [hx, spade_inv (hv.period p hp) (by simp), inv_one]
  unfold slabW; rw [Slab.spadeD, slide_basic]
  exact Slab.serial_spade ((hv.price p hp).mono (le_max_left ..)) (serial.free.mono (le_max_right ..))

def ColdRank (G : Gauge) (P : Patch) (B : Bed) (σ C : ℝ) := Freezer ((altarTile P.L (Loc G 1)).dual) (altarTile P.L _) (furnish P.L (dais G (inch P.L) B)) σ C
def ColdTone (G : Gauge) (P : Patch) (σ C : ℝ) := Freezer (altarTile P.L (Loc G 0)|>.dual) (altarTile P.L _) (throneK G P.L) σ C
lemma absoluteTone {E : Eye ι (Acts G P)} (h : ColdTone G P σ C) (he : σ≤1/128) : Freezer (altarTile P.L (Loc G 0)|>.dual) (altarTile P.L _) (grenadeFilm E).tab σ C := Freezer.passes h (fun p hp => (grenade_ground E (p:=p) (fun i => (hp i).trans_le he)).symm)

section ecology
-- coherent family. Z general, requires truth of particular Kick K; we pay with casts.
variable {m n : ℕ→Side}
structure PostCard (R : PathData G) (p : Clip) (P : Patch) (M : KernelChoices) (E : Eye ι (Acts G P))
    (X : Spark ι G P) (m n : ℕ→Side) where
    ship : Armada m n P M
    tags i : (ship.boot i).Choices
    L i : Corn (Co (m i) ι)→L[ℝ] Bang G (m i) (n i)
    bare i : ∀ x, ((L i) x).2=0
    tilts i : Turns E (billZ (ship.boot i) (L i))
    meets i : let S := ship.boot i
              Ticket X (fun v => repackM (unitSplit G S 1) (unitSplit G S 1) (flare p R (headingF S (tags i) false (L i) v)))

variable {r : Clip} {R : PathData G} {E : Eye ι (Acts G P)} {X : Spark ι G P} (Q : PostCard R r P K E X m n) (hv : P.Branches K G) (hm : Tendsto (fun i=>(m i).val) atTop atTop)
variable {η τ ε d Ω Λ A : ℝ} {B : Bed}
include hm Q hv

-- post proofs before Nano. Need ColdRank drawn from shape H._.
lemma freezeRank (h : Play (rankF E X) σ) (hp : 0<σ) (he : σ ≤ 1/128)
    (hc : R.Bounds r τ Ω Λ) (ht : Attached B R) (hy : B.metric.strip (inch P.L*σ) A)
    (hf : ∀ i,Floor B r (n i) ε d) (hw : ∀ i, Bid.Sworn B (n i) G) (hz : η≤σ) (HG : ColdRank G P B η D) : Freezer (altarTile P.L (Loc G 1)|>.dual) (altarTile P.L _) (rankF E X).tab η D := by
  let T := furnish P.L (dais G (inch P.L) B)
  have hu := mul_pos (inch_pos P.L) hp
  have hh := dais_charge (G:=G) B (inch_pos P.L) (inch_le P.L) hu (mul_le_mul_of_nonneg_left he (inch_pos _).le) hy
  refine Freezer.passes HG fun x hx => Poster.renew hh.furnish_ok h.tab hp hm ?_ (fun j => (hx j).trans_le hz : x∈strip σ)
  intro i
  let S := Q.ship.boot i
  let U := rankAux (1:Config G (n i)) r R (inch P.L)
  let M := approached (repackM (unitSplit G S 1) (unitSplit G S 1) U)
  refine ⟨M,?_,?_⟩
  · have he : Jaunt ((approached U).submatrix (splitCo S.ratio (Loc G 1)).symm (splitCo S.ratio (Loc G 1)).symm) T 0 := Jaunt.press S.ratio (daisy (inch_pos P.L) _ _ _ hc ht (hf i) (hw i) (B.metric.rights _ _ hy hu.le)) hh hp
    exact he
  have hk := rank_lyrics S (Q.tags i) false (Q.L i) (Q.tilts i) (Q.meets i) |>.tab
  have hi : headingF S (Q.tags i) false (Q.L i) 0=1 := congr_arg Prod.fst (zero_hat S hv ..)
  dsimp only [cardM] at hk; rw [hi] at hk; exact hk
omit hm hv in
lemma meterMark (hp : P.Branches K G) (i) : let S := Q.ship.boot i
    Jaunt (approached (repackM (unitSplit G S 0) (clothe G S) (postroom S (Q.tags i) (inch P.L)))) (CanonR E false).tab 0 := by
  intro S
  have hx := (regulator_tour S (Q.tags i) false (Q.L i) (Q.tilts i) hp (fun x => congr_arg Prod.fst (Q.bare i x))).tab
  unfold cardM at hx; dsimp only at hx
  rw [zero_hat S hp] at hx; exact hx

lemma freezeLegion (h : Charges (slabW G P.L|>.dual) (slabW G P.L) (legionF E false X K.penalty) σ C) (hvP : Poster σ (CanonR E false).tab) (hp : 0<σ)
    (hc : R.Bounds r τ Ω Λ) (ht : Attached B R) (hy : B.metric.strip (inch P.L*σ) A)
    (hf : ∀ i, Floor B r (n i) ε d) (hw : ∀ i,Bid.Sworn B (n i) G) (hz : η≤σ) (HG : Freezer (slabW G P.L|>.dual) (slabW G P.L) (forceK G P (CanonR E false).tab K.penalty B) η D) : Freezer (slabW G P.L|>.dual) (slabW G P.L) (legionF E false X K.penalty).tab η D := by
  let H := (CanonR E false).tab
  have hh : Poster σ (forceK G P H K.penalty B) := Poster.amounts (gift_lane B _ hy hp) (hvP.reverse.forge hvP)
  refine Freezer.passes HG fun x hx => Poster.renew hh h.covered.tab hp hm ?_ (fun j => (hx j).trans_le hz : x ∈ strip σ)
  intro i
  classical
  let S := Q.ship.boot i
  let V := Q.tags i
  let Y := clothe G S
  let Z := Q.L i
  have hp' := meterMark Q hv i
  refine ⟨approached (repackM Y Y (commonM S V r R (inch P.L))), ticket_own B hv hc ht (hw i) (hf i) hp' hp hy,?_⟩
  have hk := (legislature S V false Z (Q.tilts i) hv (fun x => congr_arg Prod.fst (Q.bare i x)) (fun x => congr_arg Prod.snd (Q.bare i x)) (Q.meets i)).tab
  dsimp only [cardM] at hk
  rw [zero_hat S hv V, map_zero] at hk; simp only [Prod.fst_zero, input_zero] at hk
  rw [legion_origin hv hc V _ (shellCost S hv V false)] at hk; exact hk

lemma freezeMedal (h : Charges (slabW G P.L|>.dual) (slabW G P.L) (medalF E false X K.penalty) σ C) (hvP : Poster σ (CanonR E false).tab) (hp : 0<σ)
    (hc : R.Bounds r τ Ω Λ) (ht : Attached B R) (hy : B.metric.strip (inch P.L*σ) A)
    (hf : ∀ i, Floor B r (n i) ε d) (hw : ∀ i,Bid.Sworn B (n i) G) (hz : η≤σ) (HG : Freezer (slabW G P.L|>.dual) (slabW G P.L) (forceK G P (CanonR E false).tab K.penalty B) η D) : Freezer (slabW G P.L|>.dual) (slabW G P.L) (medalF E false X K.penalty).tab η D := by
  let H := (CanonR E false).tab
  have hh : Poster σ (forceK G P H K.penalty B) := Poster.amounts (gift_lane B _ hy hp) (hvP.reverse.forge hvP)
  refine Freezer.passes HG fun x hx => Poster.renew hh h.covered.tab hp hm ?_ (fun j => (hx j).trans_le hz : x ∈ strip σ)
  intro i
  classical
  let S := Q.ship.boot i
  let V := Q.tags i
  let Y := clothe G S
  let Z := Q.L i
  have hp' := meterMark Q hv i
  refine ⟨approached (repackM Y Y (commonM S V r R (inch P.L))), ticket_own B hv hc ht (hw i) (hf i) hp' hp hy,?_⟩
  have hk := (rewarded S hv V false Z hc (fun x => congr_arg Prod.fst (Q.bare i x)) (Q.tilts i) (Q.meets i)).tab
  dsimp only [cardM] at hk; rw [zero_hat S hv V, map_zero] at hk; simp only [Prod.fst_zero, input_zero] at hk; exact hk
end ecology
end YM.Stationary
end
