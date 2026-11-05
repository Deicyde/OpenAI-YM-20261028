import YM.Next.STATIONARY.Films.Contact
import YM.Next.STATIONARY.Shape.Rank



set_option autoImplicit false
/-!
# Kinetic Card stamp over coherent representatives. Leverages soft curvature
budgets. Phases real sheet of Θ, tags intact.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {σ η A C D E τ : ℝ} {c f : Side} {m n : ℕ→ Side}
lemma upper_glue {α β ι : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι] {K : Leagues ι α β} {M : OperatorF ι c α β} (h : Memo M 0) (hp : ∀ n≤2,∀ (p : Fin n → Momentum) (i : Fin n→ι) (v : Fin n→ Site c), (∀ j, rolls (mon (v j)) (p j)) → Jaunt (art M n (fun j => relay (v j) (i j))) (K n p i) (∑ j,v j)) : Ticket (recitalX K) M := by
  refine ⟨h,?_,fun i p q he => ?_, fun i j p q a b he hx => ?_⟩
  · rw [← art_zero]
    have hx := hp 0 (by decide) ![] ![] ![] (by rintro ⟨k,h⟩; omega); simpa only [show (fun j => relay (m:=c) ((![]:Fin 0→_) j) ((![]:Fin 0→ι) j))=![] from Subsingleton.elim ..,sum_empty,Finset.univ_eq_empty,recitalX] using hx
  · unfold seat; change Jaunt _ (K 1 ![q] ![i]) p
    have ht := hp 1 (by decide) ![q] ![i] ![p] (fun j => by fin_cases j; exact he)
    rw [show (fun j => relay ((![p]:Fin 1 → _) j) ((![i]:Fin 1 → _) j))= ![relay p i] by ext1 k; fin_cases k; rfl,Fin.sum_univ_one] at ht; exact ht
  unfold cart; change Jaunt _ (K 2 ![a,b] ![i,j]) _
  have ht := hp 2 le_rfl ![a,b] ![i,j] ![p,q] (fun k => by fin_cases k; exact he; exact hx)
  rw [show (fun k => relay ((![p,q]:Fin 2→_) k) ((![i,j]:Fin 2→_) k))=![relay p i,relay q j] by ext1 k; fin_cases k <;> rfl,Fin.sum_univ_two] at ht; exact ht

lemma ticket_glide {S : StepData c f} {Φ : Bridge G S.patch} {U : ∀ n,Mockup G n} {W : Matrix (Body 1 f) (Body 1 c) ℝ} (h : Premise S W Φ) (hp : R.Bounds p η C A)
    (he : Fruit U (inch S.patch.L * σ) D) (hc : ∀ i, i≤2 → Bitter (melon i) (U i) (creme i) (intended p R (m:=f))) (hs : 0<σ) :
    Ticket (RippleF U Φ) (FireMat p R (uniformM W) (unitSplit G S 1)) := by
  -- align S.ratio.count definitional weights.
  let X := FireMat p R (uniformM (G:=G) W) (B:= (show Lines G f 1 ≃ Co c (Co S.patch.L (Loc G 1)) from unitSplit G S 1))
  have hv : Memo X 0 := play_memo _ _ (fireCont f hp) (flare_bank _ _ hp)
  refine upper_glue hv (K:=fun n => if n≤2 then ripple Φ (melon n) (U n) else 0) (fun n hn v b q hQ => ?_); rw [if_pos hn]; exact wave_skim S Φ W _ _ h hp (he n hn) (hc n hn) hs v b q hQ

def garden {p : Clip} {R : PathData G} (S : Armada m n P K) (t : ∀ i, (S.boot i).Choices) {Φ : Bridge G P} {U : ∀ n,Mockup G n}
    (W : ∀ i, Matrix (Body 1 (n i)) (Body 1 (m i)) ℝ) (h : ∀ i, Premise (S.boot i) (W i) Φ) (hv : R.Bounds p τ D E) (hp : Fruit U (inch P.L*σ) A)
    (he : Syrupy (fun i => intended p R (m:=n i)) U) (hw : 0<σ) : PostCard R p P K (arriving Φ) (RippleF U Φ) m n :=
    ⟨S,t, fun i => cardHand (W i), fun _ _=> rfl, fun i => atlas_photo _ (h i), fun i => ticket_glide (h i) hv hp (he i) hw⟩
-- Choose stir AFTER classical recurrence caps/s but before drifts and clocks. Width η input bought from L growth only.

theorem tideMark (G : Gauge) (σ M ε Z τ A : ℝ) (hs : 0<σ) (hM : 0≤M) (hz : 0≤Z) (ht : 0<τ) (hA : 0≤A) :
    ∃ η K : ℝ,0<η ∧ 0≤K ∧ ∀ (m : ℕ→Side), Tendsto (fun i => (m i).val) atTop atTop → ∀ (p : Clip) (R : PathData G) (B : Bed) (Λ : ℝ), p.direct ≤ Z → R.Bounds p τ A Λ → Attached B R → (∀ i, Floor B p i ε M) → (∀ i, Bid.Sworn B (m i) G) →
      B.metric.strip σ M → ∃ U : ∀ n, Mockup G n, Fruit U η K ∧ Syrupy (fun i => intended p R (m:=m i)) U := by
  obtain ⟨P,hP,H⟩ := whiteWilson G
  obtain ⟨x,T,hx,hT,W⟩ := greyson G σ ε M Z τ A hs hM hz ht hA
  obtain ⟨w,Q,hw,hQ,E⟩ := blenderBar G (lt_min zero_lt_one hx)
  refine ⟨w,(T+P)*Q,hw,by positivity,fun m hm p R B Λ hp hv h hF hD hx' => ?_⟩
  refine E _ (by positivity) m _ (fun i => ⟨(strain p R hv).analytic,pact (m:=m) hv h (fun i=>hF (m i)) hD i⟩) ?_
  intro k hk he
  let V i := WilsonQ G (m i)
  let F i := intended p R (m:=m i)
  change Drinkable k m F _ _ _
  rw [show F=F-V+V from (sub_add_cancel F V).symm]
  refine ((W m hm B p R Λ hv h hx' hp hF hD _ hk he).thins (lt_min zero_lt_one hx) (min_le_right ..) le_rfl (by omega)).more ((H m hm _ hk he).thins (lt_min zero_lt_one hx) (min_le_left ..) le_rfl le_rfl) (fun i => (strain _ _ hv).analytic.sub Wilson_witness.analytic) (fun i=> Wilson_witness.analytic)
end YM.Stationary
end

/-!
# Fine momentum calculation.

Infrared inputs WITHOUT block. TabB/SpotB/archB tied to taste at same m.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {σ η A C D ε : ℝ} {c m : Side} {n t : ℕ}

abbrev Fslot (G : Gauge) := Loc G 1
abbrev Foot (G : Gauge) := Loc G 0
abbrev KindF (G : Gauge) := Film (Fslot G) (Fslot G) (Fslot G)
abbrev KindG (G : Gauge) := Film (Fslot G) (Foot G) (Foot G)

end YM.Stationary
end

/-!
# `Fine Momentum` ticket of literal raw flare. No polynomial rho specialization
 implicit. Tilts at input true path norm, even if periods fixed sparse. Arch
 costs lease without Ward on masked portion.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {σ η A C D ε : ℝ} {c m : Side} {n t : ℕ}

lemma Jaunt.atmosphere {U : CircM m α β} {F : Momentum→ CompM α β} {k : Site m} (h : ∀ p q,rolls (mon (p:Site m)) q → ∀ (v : β) (t : Site m) (i : α),
    dotProduct (relay t i) (U *ᵥ relay p v) = if t+(p+k)=0 then (Fintype.card (Site m):ℂ)*F q i v else 0) : Jaunt U F k := by
  have hr {α : Type} [Fintype α] [DecidableEq α] (b : Phase α) (k : Site m) : tune k b=∑ i,b i • relay k i := by ext1 i; rw [Finset.sum_apply]; simp [tune,relay,Pi.single_apply,mul_comm]
  intro p q hp v; apply ray_book; intro j b
  have he (x : β) (i : α) : dotProduct (relay j i) (U *ᵥ relay p x)=dotProduct (relay j i) (tune (p+k) (F q*ᵥ (Pi.single x 1))) := by
    rw [h p q hp x j,relay, ray_dots]; split; next hh => rw [single_one_dotProduct,mulVec_single]; simp
    rfl
  have hv x : dotProduct (tune j b) (U*ᵥ relay p x)=dotProduct (tune j b) (tune (p+k) (F q*ᵥ (Pi.single x 1))) := by rw [hr b,sum_dotProduct,sum_dotProduct]; simp_rw [smul_dotProduct,he]
  let a := tune j b
  rw [hr v,mulVec_sum,dotProduct_sum]; simp_rw [Matrix.mulVec_smul,dotProduct_smul,hv]
  suffices ht : tune (p+k) (F q*ᵥ v)=∑ x,v x • tune (p+k) (F q*ᵥ (Pi.single x 1)) by simp only [ht,dotProduct_sum,dotProduct_smul]
  ext1 i; rw [Finset.sum_apply]; simp [Matrix.mulVec,dotProduct,tune, Finset.mul_sum,mul_left_comm]; refine sum_congr rfl fun _ _ => ?_; ring

def caftan {α : Type} (χ : Breed t (Axis → α)) (x : Keys t) := χ x.1.succ x.2
def chaperon (K : Picture G t) (b : Breed t (Loc G 1)) (u : Breed t Momentum) := K (Prod.snd∘b) (Prod.fst∘b) (caftan u)
lemma drinkLocate (b : Breed t (Loc G 1)) (u : Breed t (Site m)) (q : Breed t Momentum) (hq : ∀ i, rolls (mon (u i)) (q i)) {v : Breed t Bool} {F : Link G m→ℝ} {K : Picture G t} (hv : DrinkIt K F v) (ht : ∀ i j, Firm σ A (K i j)) : liquid v F (fun i=> relay (u i) (b i))= if ∑ i,u i=0 then (Fintype.card (Site m):ℂ)*chaperon K b q else 0 := by
  rw [show (fun i=>relay (u i) (b i))=glyph u (Prod.snd ∘ b) (Prod.fst ∘ b) from rfl,hv (Prod.snd ∘ b) (Prod.fst ∘ b) u,collected]; split
  next hp => unfold chaperon; rw [(show rolls (outphase u) (caftan q) from rolls_keys fun i=> hq i.succ).apply (ht (Prod.snd∘b) (Prod.fst∘b)) ((ht (Prod.snd∘b) (Prod.fst∘b)).in_range (out_real u))]
  rfl

def wineShift (q : Fin n→Momentum) (p : Momentum) : Fin (n+2)→ Momentum := duoTop n q (-(p+∑ j,q j)) p
def wineM (K : Picture G (n+1)) (q : Fin n→ Momentum) (b : Fin n→Loc G 1) (p : Momentum) := of fun i j=> chaperon K (duoTop n b i j) (wineShift q p)

def vintage (F : Picture G 1) (H : Picture G 2) (T : Picture G 3) : KindF G where
  tab := wineM F (![]:Fin 0→_) ![]
  spot i p := wineM H (![p] : Fin 1 →_) (![i])
  arch i j p q := wineM T (![p,q]:Fin 2 →_) (![i,j])

variable (p R)
abbrev fineFlare (x : Link G m) := flare p R (input G m x)
variable {p R}
lemma vintage_sips (v : Fin n→ Momentum) (b : Fin n→Site m) (i : Fin n→Fslot G) (he : ∀ j,rolls (mon (b j)) (v j)) {K : Picture G (n+1)} (h : ∀ i j, Firm σ A (K i j))
    (hv : DrinkIt K (intended (m:=m) p R) (creme n)) (hp : R.Bounds p η C D) : Jaunt (art (fineFlare p R) n (fun j=> relay (b j) (i j))) (wineM K v i) (∑ j,b j) := by
  let B : Picture G (n+1):=K
  let i₀ := Equiv.refl (Lines G m 1)
  let V := LinearMap.id (R:=ℂ) (M:=Phase (Lines G m 1))
  let U := ContinuousLinearMap.id ℝ (Link G m)
  refine Jaunt.atmosphere (fun x q hx b' t a => ?_)
  let W := fun j=> relay (b j) (i j)
  have hs : dotProduct (relay t a) (art (fineFlare (m:=m) p R) n W*ᵥ relay x b')=_ := published U i₀ V (fun _=> rfl) hp _ _ _
  let y := duoTop n b t x
  let k := duoTop n i a b'
  rw [hs,show (duoTop _ _ _ _:Fin (n+2)→Phase (Lines G m 1))=(fun i=>relay (y i) (k i)) from ?_]
  swap
  · ext1 i; cases i using Fin.lastCases with
    | last => simp [duoTop,y,k]; rfl
    | cast i => cases i using Fin.lastCases with
      | last => simp [duoTop,y,k]; rfl
      | cast i => simp [duoTop,y,k]; rfl
  have ht : ∑ i,y i = t+(x+∑ i,b i) := by
    unfold y duoTop; rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc,Fin.snoc_last]; rw [Fin.sum_univ_castSucc]; simp only [Fin.snoc_castSucc,Fin.snoc_last]; abel
  by_cases ha : t+(x+∑ i,b i)=0
  · rw [drinkLocate k y (wineShift v q) ?_ hv h,ht]; rfl
    intro j
    unfold wineShift y duoTop; cases j using Fin.lastCases with
    | last => simpa using hx
    | cast j => simp only [Fin.snoc_castSucc]
                cases j using Fin.lastCases with
                | last => rw [Fin.snoc_last, Fin.snoc_last, eq_neg_of_add_eq_zero_left ha]; exact (hx.combine (collide b v he)).flip_sign
                | cast j => simpa using he j
  rw [drinkLocate k y (mon ∘ y) (fun j=> rolls.refl _) hv h,ht,if_neg ha,if_neg ha]

lemma epic {F : Picture G 1} {H : Picture G 2} {T : Picture G 3} (hF : ∀ i j, Firm σ A (F i j)) (hH : ∀ i j, Firm σ A (H i j)) (hT : ∀ i j, Firm σ A (T i j))
    (hp : R.Bounds p η C D) (hf : DrinkIt F (intended (m:=m) p R) (creme 0)) (hh : DrinkIt H (intended (m:=m) p R) (creme 1)) (ht : DrinkIt T (intended (m:=m) p R) (creme 2)) : Ticket (vintage F H T) (fineFlare p R (m:=m)) := by
  let U := ContinuousLinearMap.id ℝ (Link G m); let i := Equiv.refl (Lines G m 1)
  let V := FireMat p R U i
  refine ⟨(show Memo V 0 from play_memo _ _ (fireCont _ hp) (flare_bank _ _ hp)), ?_,?_,?_⟩
  · have he := vintage_sips (![]:Fin 0→_) ![] ![] (fun i=>Fin.elim0 i) hF hf hp
    rw [show (fun j : Fin 0=> (relay ((![]:Fin 0→Site m) j) ((![]:Fin 0→Fslot G) j)))=![] from Subsingleton.elim ..,art_zero] at he
    simp only [sum_empty,Finset.univ_eq_empty] at he; exact he
  · intro i a p hp'; have he := vintage_sips (![p]:Fin 1→Momentum) ![a] ![i] (fun j=> by fin_cases j; exact hp') hH hh hp
    rw [show (fun j=>relay ((![a]:Fin 1→_) j) ((![i]:Fin 1 → Loc G 1) j))= ![relay a i] by ext1 b; fin_cases b; rfl,Fin.sum_univ_one] at he; exact he
  intro i j a b q r hq hr; have he := vintage_sips (![q,r]:Fin 2→Momentum) ![a,b] ![i,j] (fun k=> by fin_cases k; exact hq; exact hr) hT ht hp
  rw [show (fun z=>relay ((![a,b]:Fin 2 →_) z) ((![i,j]:Fin 2 → Loc G 1) z))= ![relay a i,relay b j] by ext1 x; fin_cases x <;> rfl,Fin.sum_univ_two] at he; exact he
end YM.Stationary
end

/-!
Uniform strip components of `WineM` with widths chosen at the actual
input τ. No continuum-comparison claim implicit in soft markings.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {σ η A C D E ε : ℝ} {c m : Side} {n t : ℕ}

lemma beer_contour (b : Picture G (n+1)) (h : ∀ i j,Firm σ A (b i j)) : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y] (z : Y) (v : Y → Fin n→Momentum) (q : Y → Momentum) (hv : DifferentiableAt ℂ v z) (hq : DifferentiableAt ℂ q z), (∀ i,v z i∈ strip σ) → q z∈strip σ → q z+∑ i,v z i ∈strip σ → ∀ i, BillD (fun x=> wineM b (v x) i (q x)) z := by
  intro Y _ _ z v q hv hq h1 h2 h3 i x y
  let p (a : Y) := wineShift (v a) (q a); let l a : Space (n+1) := caftan (p a)
  have hk : ∀ j,p z j ∈ strip σ := by
    intro k; cases k using Fin.lastCases with
    | last => simpa [p,wineShift,duoTop] using h2
    | cast k => cases k using Fin.lastCases with
      | last => simpa [p,wineShift,duoTop] using negResident h3
      | cast k => simpa [p,wineShift,duoTop] using h1 k
  have hl (j : Fin (n+2)) : DifferentiableAt ℂ (fun x=>p x j) z := by
    unfold p wineShift duoTop; cases j using Fin.lastCases with
    | last => simpa using hq
    | cast k => simp only [Fin.snoc_castSucc]
                cases k using Fin.lastCases with
                | last => simp only [Fin.snoc_last]; exact (hq.add (DifferentiableAt.fun_sum fun k _ => differentiableAt_pi.mp hv k)).neg
                | cast k => simp only [Fin.snoc_castSucc]; exact differentiableAt_pi.mp hv k
  let r := duoTop n i x y
  apply DifferentiableAt.comp (g:=b (Prod.snd∘r) (Prod.fst∘r)) (f:=l) z ((h _ _).1.hol (l z) (fun i=> hk i.1.succ i.2))
  exact differentiableAt_pi.mpr fun i => differentiableAt_pi.mp (hl i.1.succ) i.2

lemma beer_roll (b : Picture G (n+1)) (h : ∀ i j,Firm σ A (b i j)) (v w : Fin n→Momentum) (p q : Momentum) (he : ∀ i,rolls (v i) (w i)) (hp : rolls p q) (hx : ∀ i,v i∈strip σ) (hw : p∈strip σ) (hv : p+∑ i,v i ∈ strip σ) (i) : wineM b v i p=wineM b w i q := by
  have hL (j) : rolls (wineShift v p j) (wineShift w q j) ∧ wineShift v p j∈strip σ := by
    cases j using Fin.lastCases with
    | last => simp only [wineShift,duoTop,Fin.snoc_last]; exact ⟨hp,hw⟩
    | cast j => cases j using Fin.lastCases with
      | last => simp only [wineShift,duoTop,Fin.snoc_castSucc,Fin.snoc_last]; refine ⟨(hp.plus ?_).neg,negResident hv⟩
                suffices ht : ∀ t : Finset (Fin n), rolls (∑ i∈t,v i) (∑ i∈t,w i) from ht univ
                intro t; induction t using Finset.induction with
                | empty => rw [sum_empty, sum_empty]; exact rolls.refl _
                | insert a l hl ih => rw [sum_insert hl,sum_insert hl]; exact (he a).plus ih
      | cast j => simp only [wineShift,duoTop,Fin.snoc_castSucc]; exact ⟨he j,hx j⟩
  ext1 j k; let r := duoTop n i j k
  exact rolls.apply (p:=caftan (t:=n+1) (wineShift v p)) (q:=caftan (wineShift w q)) (rolls_keys fun j=> (hL _).1) (h (Prod.snd∘r) (Prod.fst∘r)) fun a=> (hL _).2 a.2

lemma wine_play (F : Picture G 1) (H : Picture G 2) (T : Picture G 3) (hF : ∀ i j,Firm σ A (F i j)) (hH : ∀ i j,Firm σ C (H i j)) (hT : ∀ i j,Firm σ D (T i j)) : Play (vintage F H T) σ := by
  refine ⟨⟨fun w => beer_contour F (n:=0) hF _ (fun _ => ![]) (fun x=>x) (differentiableAt_const _) differentiableAt_id (fun i=>Fin.elim0 i) w (by simpa using w) ![], fun {p q} he hv => beer_roll F (n:=0) hF ![] ![] p q (fun i =>Fin.elim0 i) he (fun i => Fin.elim0 i) hv (by simpa using hv) ![] ⟩,fun i=> ⟨?_,?_⟩,fun i j=> ⟨?_,?_⟩ ⟩
  · intro p q w
    refine beer_contour H (n:=1) hH (p,q) (fun z=> ![z.1]) Prod.snd (differentiableAt_pi.mpr (fun i=> ?_)) differentiableAt_snd (fun i=> ?_) w.basic ?_ ![i]
    · fin_cases i; exact differentiableAt_fst
    · fin_cases i; exact w.side
    simpa using w.added
  · intro p p' q q' he hu hv; refine beer_roll H (n:=1) hH ![p] ![p'] q q' (fun i=> ?_) hu (fun i=> ?_) hv.basic (by simpa using hv.added) ![i]
    · fin_cases i; exact he
    fin_cases i; exact hv.side
  · intro p q r hv
    refine beer_contour T (n:=2) hT (p,q,r) (fun z=> ![z.1,z.2.1]) (fun z=> z.2.2) (differentiableAt_pi.mpr (fun i=> ?_)) (by fun_prop) (fun i=> ?_) hv.oneWay.basic (by rw [Fin.sum_univ_two]; exact hv.total) _
    · fin_cases i; exact differentiableAt_fst; change DifferentiableAt ℂ (fun z : Momentum × Momentum × Momentum => z.2.1) _; fun_prop
    fin_cases i; exact hv.oneWay.side; exact hv.second.side
  intro p p' q q' r r' h1 h2 h3 hv; refine beer_roll T (n:=2) hT ![p,q] ![p',q'] r r' (fun i=> ?_) h3 (fun i=> ?_) hv.oneWay.basic (by rw [Fin.sum_univ_two]; exact hv.total) _
  · fin_cases i; exact h1; exact h2
  fin_cases i; exact hv.oneWay.side; exact hv.second.side

end YM.Stationary
end

/-!
# Mail sector unblocked, literal Fine links. True amplitude trigonometric
poly. No periodic positivity assumptions external. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {α β : Type} [Fintype α] [DecidableEq α] {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {q : Momentum} {σ η A C D ε : ℝ} {m : Side} {n : ℕ}

-- scatter on F TYPE. Note x slot convention TypeFace ≃ Axis

def delocalF (a : TypeFace 1) (G : Gauge) : Corn (Fslot G)→L[ℝ] G.Color :=
    (show G.Color ≃L[ℝ] Corn G.ColorIndex from (WithLp.linearEquiv 2 ℝ _).toContinuousLinearEquiv).symm.toContinuousLinearMap ∘L (ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (a,i))

def pummel (i j : Fslot G) (x : Corn (Fslot G)) := if i.1=j.1 then scattering G (G.lieExp (delocalF i.1 G x)) i.2 j.2 else 0
def patina (G : Gauge) : Leagues (Fslot G) (Fslot G) (Fslot G) := fun k _ b _=> of fun i j=> beat (pummel i j) 0 k (fun l=>Pi.single (b l) 1)
def firstB (G : Gauge) : KindF G := recitalX (patina G)
lemma pummel_diff (i j : Fslot G) : AnalyticAt ℝ (pummel i j) 0 := by
  unfold pummel; split; next e =>
    let L := delocalF i.1 G; exact (ContDiffAt.comp (g:=fun u : G.Color => scattering G (G.lieExp u) i.2 j.2) (f:=L) (0: Corn (Fslot G)) (by rw [map_zero]; exact scat_rate ..) L.contDiff.contDiffAt).analyticAt
  exact analyticAt_const
lemma pummel_at (i j : Lines G m 1) (x : Link G m) : motley (input G m x) i j= if i.1=j.1 then pummel i.2 j.2 (fun v=> x (i.1,v)) else 0 := by
  unfold motley; simp only [Matrix.of_apply, ite_and]; split; swap; rfl
  unfold pummel; split; swap; rfl
  rw [input_color, show edgeColor x _=delocalF i.2.1 G (fun v=> x (i.1,v)) from ?_]
  ext k; change x (i.1,coord (axisEquiv.symm i.2.1),k)=x (i.1,i.2.1,k); rw [show coord (axisEquiv.symm i.2.1)=_ from axisEquiv.apply_symm_apply _]

abbrev ScatterAll (x : Link G m) := motley (input G m x)
lemma pulp (v : Fin n→Site m) (b : Fin n→Fslot G) (X : Fin n→Momentum) (y : Momentum) (i j : Lines G m 1) : art (ScatterAll (m:=m)) n (fun k=>relay (v k) (b k)) i j= if i.1=j.1 then cell (∑ k,v k) i.1*patina G n X b y i.2 j.2 else 0 := by
  unfold art; rw [Matrix.of_apply]; simp_rw [ScatterAll,pummel_at i j]; split; swap; · simp [beat,enlarge,recording_apply]
  let L : Link G m →L[ℝ] Corn (Fslot G) := ContinuousLinearMap.pi fun b=>ContinuousLinearMap.proj (i.1,b)
  let T : Phase (Lines G m 1)→ₗ[ℂ] Phase (Fslot G) := LinearMap.pi fun b=>LinearMap.proj (i.1,b)
  change beat (pummel i.2 j.2 ∘ L) _ _ _=_
  rw [evaluated (L:=L) T (fun p=>rfl) (pummel_diff i.2 j.2), MultilinearMap.compLinearMap_apply, show (fun k=> T (relay (v k) (b k)))= (fun k=> cell (v k) i.1 • (Pi.single (b k) 1)) from rfl, MultilinearMap.map_smul_univ,cell_hom]; rfl
lemma patina_books : Ticket (firstB G) (ScatterAll (m:=m)) := by
  refine all_ground (fun i j=> ?_) fun n p i v _ q k _ x=> ?_
  · simp_rw [ScatterAll,pummel_at i j]; split
    · let L : Link G m →L[ℝ] Corn (Fslot G) := ContinuousLinearMap.pi fun b=>ContinuousLinearMap.proj (i.1,b)
      exact (show ContDiffAt ℝ ω (pummel i.2 j.2) (L 0) by rw [map_zero]; exact (pummel_diff ..).contDiffAt).comp (f:=L) _ L.contDiff.contDiffAt
    exact contDiffAt_const
  ext1 a; unfold tune Matrix.mulVec dotProduct
  rw [Fintype.sum_prod_type];
  simp_rw [pulp _ i p k]
  rw [Finset.sum_eq_single a.1]
  · simp [Finset.mul_sum]; rw [cell_duality (q+_),cell_add,cell_duality a.1,cell_duality a.1]
    refine sum_congr rfl fun i _ => ?_; ring
  · intro l _ he; simp [Ne.symm he]
  simp

abbrev KindS (G : Gauge) := Film (Fslot G) (Fslot G) (Foot G)

def firstRay (G : Gauge) : KindS G := Film.cardF (-(pageD G 0))
def dashboard (G : Gauge) := ∑ i : Axis, (dasher G i)ᵀ
def boardF (G : Gauge) : KindS G := Film.cardF (fun q => dashboard G + pageD G 0 q)
def matina (G : Gauge) : KindS G := (firstRay G).plus ((firstB G).pay (boardF G))

lemma matina_green : Play (matina G) σ := by
  have hx : Play (firstB G) σ := ⟨Poster.web _,fun _ => ⟨fun _ => BillD.park _ _,fun _ _ _ =>rfl⟩,fun _ _=> ⟨fun _ => BillD.park _ _,fun _ _ _ _=>rfl⟩⟩
  have h : Poster σ (firstRay G).tab := by
    have hh := Poster.plus_nec (σ:=σ) (f:=pageD G 0) (page_linen 0) (-1); simp only [neg_smul,one_smul] at hh; exact hh
  exact Play.plus (Play.current h) (hx.pay (Play.current ((Poster.web _).amounts (page_linen 0))))

abbrev pelt (x : Link G m) := mail (input G m x)
lemma pelt_at : Jaunt (approached (mail (1:Config G m))) (firstRay G).tab 0 := by
  rw [mailed_zero,prom_negation]; exact (page_read m 0).backside
lemma boardJump : Ticket (boardF G) (fun _:Link G m=>shiftLaunch G m) := by
  have he i := (dash_far (G:=G) (n:=m) i).takes
  let V := (restaged G m)
  have hh : approached V=∑ i:Axis,(approached (stagehand i G m))ᵀ := by ext; simp [V,approached,restaged,Matrix.sum_apply]
  have hx := Jaunt.summations univ _ (fun i _=> he i)
  have ht : Jaunt (approached V) (fun p:Momentum=> dashboard G) 0 := by
    rw [hh]; convert hx using 1; ext1 i; rw [Finset.sum_apply]; rfl
  apply Ticket.current; unfold shiftLaunch; rw [sub_eq_add_neg,prom_addition,prom_negation]
  have hp := ht.plus (pelt_at (G:=G) (m:=m)|>.backside); simp only [firstRay,Film.cardF,neg_neg] at hp; exact hp
lemma pelt_ticket : Ticket (matina G) (pelt (m:=m)) := by
  classical
  refine Ticket.foreign (Ticket.plus (Ticket.current _ _ pelt_at) (Ticket.pay patina_books boardJump)) ?_
  refine Eventually.of_forall fun x => ?_; exact (vivid _).symm
end YM.Stationary
end

/-!
# Precise film rings for unblocked precision. Component formulas valid
on all cofinal meshes. Ticket identity local kernel determinant, no actual strip
 tilt on joint Hessian imported from that calculation. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {q : Momentum} {σ η A C D ε μ : ℝ} {m : Side} {n : ℕ}

section names
variable (G μ)

def quarry : KindG G := (matina G).rear.pay (matina G)
def cinder : KindG G := (quarry G).plus (Film.cardF (fun _ => ((μ^2:ℝ):ℂ) • 1))
def chert : KindG G := ((cinder G μ).back).weight ((μ^2:ℝ):ℂ)
def chisel : KindG G := (tripleFilm (tripleFilm (chert G μ))).weight ((μ^2:ℝ):ℂ)
def coring : KindG G := (quarry G).plus (chisel G μ)
def stony (i : Axis) := let F := Film.cardF (ι:=Fslot G) (fun _ => dasher G i); (F.rear.pay (chisel G μ)).pay F
def graniteF := chore (List.finRange 4) (stony G μ)
def granary (T : KindF G) := T.plus ((matina G).pay (matina G).rear)
def massif (T : KindF G) : KindF G := (granary G T).plus (graniteF G μ)
def amena (G : Gauge) (S : KindF G) : Award G := ((↑(1/2:ℝ)):ℂ) • (massif G μ S).figure-(coring G μ).figure
end names

section real
lemma quarry_g : Ticket (quarry G) (fun x => tonic (input G m x)) := pelt_ticket.rear.pay pelt_ticket
lemma crumb : Ticket (cinder G μ) (fun x=>ammo μ (input G m x)) := by
  have he : Jaunt (m:=m) (approached (μ^2 • (1:Matrix (Lines G m 0) (Lines G m 0) ℝ))) (fun _ => ((μ^2:ℝ):ℂ) • (1:CompM (Foot G) (Foot G))) 0 := by rw [prom_tone,prom_one']; exact Jaunt.smul Jaunt.noop _
  exact quarry_g.plus (Ticket.current _ _ he)
lemma grain (h : 0<μ) : Ticket (chert G μ) (fun x=> pebble μ (input G m x)) :=
    let H := crumb (μ:=μ) (G:=G) (m:=m); by exact (H.back (fund_det (ammo_safe (input G m 0) h))).weight _
lemma grantY (h : 0<μ) : Ticket (chisel G μ) (fun x=> cannon μ (input G m x)) := by
  let M := fun x => pebble μ (input G m x)
  refine ((triple_am _ (fun x => M x^3) (triple_am _ M (grain h))).weight (μ^2)).foreign ?_; filter_upwards with x
  change μ^2 • (M x^3)^3= _; rw [← pow_mul]; rfl
lemma grot (h : 0<μ) : Ticket (coring G μ) (fun x=>grenade μ (input G m x)) := quarry_g.plus (grantY h)
lemma grantV (h : 0<μ) : Ticket (graniteF G μ) (fun x=> brigadeM (cannon μ (input G m x))) := by
  let M i x := (stagehand i G m)ᵀ*cannon μ (input G m x)*stagehand i G m
  have hv i : Ticket (stony G μ i) (M i) :=
    let F := Ticket.current (ι:=Fslot G) (fun _ => dasher G i) (stagehand i G m) (dash_far i); (F.rear.pay (grantY h)).pay F
  refine (choreRuns (List.finRange 4) (U:=M) (fun i _=> hv i)).foreign ?_; filter_upwards with x; rw [← Fin.sum_univ_def M,Finset.sum_apply]; rfl
lemma grantM {T : KindF G} (h : Ticket T (fineFlare p R (m:=m))) (hp : 0 < μ) : Ticket (massif G μ T) (fun x=>rankAux (input G m x) p R μ) :=
    let F := pelt_ticket (G:=G) (m:=m); (h.plus (F.pay F.rear)).plus (grantV hp)

lemma gemF {T : KindF G} {B : Bed} {E} (h : Ticket T (fineFlare p R (m:=m))) (hp : R.Bounds p σ A D) (ht : Floor B p m ε E) (hg : Attached B R) (hx : Bid.Sworn B m G) (hm : 0<μ) : Awards (amena μ G T) (PoleTest p R μ (n:=m)) := by
  let P := fun x => rankAux (input G m x) p R μ
  let V := fun x => grenade μ (input G m x)
  have he : IsUnit (P 0).det := by unfold P; rw [input_zero]; exact fund_det (rank_positive μ hp ht hg hx hm)
  have hp' : IsUnit (V 0).det := fund_det (grenade_safe _ hm)
  -- re-use without determinant factor mutation
  have H := ring_award (Equiv.refl _) (Equiv.refl _) (A:=P) (B:=V) (grantM h hm) (grot hm) he hp'
  exact H
end real

section scope
lemma quarry_p : Play (quarry G) σ := matina_green.rear.pay matina_green
lemma cinder_fresh : Play (cinder G μ) σ := quarry_p.plus (Play.current (Poster.web _))

lemma crumbly (h : 0<σ) : ∀ i∈strip σ, (cinder G μ).tab i=soda μ i • 1 := by
  apply Poster.renew cinder_fresh.tab (ammo_poster (G:=G)) h walentes
  refine fun i => ⟨_,(crumb (G:=G) (μ:=μ) (m:=walent i)).tab, ?_⟩
  rw [cardM,input_zero]; exact tonic_soda _
lemma cobble (h : 0 < μ) (hp : μ ≤ 1) : ∀ i∈strip (μ*(1/128:ℝ)), IsUnit ((cinder G μ).tab i).det := fun i hi => by
    rw [crumbly (by positivity) i hi,det_smul]; simpa using (soda_glass h hp hi).isUnit.pow (Fintype.card (Foot G))
lemma fleck (h : 0<μ) (hp : μ≤1) : Play (chisel G μ) (μ*(1/128:ℝ)) :=
    (triple_paid _ (triple_paid _ ((cinder_fresh.back (cobble h hp)).weight _))).weight _
lemma flake (h : 0<μ) (hp : μ≤1) : Play (coring G μ) (μ*(1/128:ℝ)) := quarry_p.plus (fleck h hp)
lemma flakeTabs (h : 0 < μ) (hp : μ≤1) : ∀ i∈ strip (μ*(1/128:ℝ)), (coring G μ).tab i=throneF G μ i := by
  apply Poster.renew (flake h hp).tab (throne_rate h hp) (by positivity) walentes
  refine fun i=> ⟨_,(grot (m:=walent i) (G:=G) h).tab,?_⟩; rw [cardM,input_zero]; exact tonic_throne _ h
lemma granite_green (h : 0<μ) (hp : μ≤1) : Play (graniteF G μ) (μ*(1/128:ℝ)) := by
  have he i : Play (stony G μ i) (μ*(1/128:ℝ)) :=
    let L := (Play.current (ι:=Fslot G) (σ:=μ*(1/128:ℝ)) (Poster.web (dasher G i))); (L.rear.pay (fleck h hp)).pay L
  exact choreL _ (fun i _ => he i)
lemma massif_green {F : KindF G} (h : 0<μ) (hp : μ≤1) (he : σ≤μ*(1/128:ℝ)) (hv : Play F σ) : Play (massif G μ F) σ := (hv.plus (matina_green.pay matina_green.rear)).plus ((granite_green h hp).mono he)
lemma massifTabs {T : KindF G} {E : ℝ} {m : ℕ→Side} {B : Bed} (h : Play T σ) (he : Tendsto (fun i => (m i).val) atTop atTop)
    (hf : ∀ i, Ticket T (fineFlare p R (m:=m i))) (hX : R.Bounds p η A C) (hq : Floor B p 1 ε E)
    (hy : ∀ i,Floor B p (m i) ε E) (hF : Attached B R) (hB : ∀ i,Bid.Sworn B (m i) G) (hΩ : B.metric.strip σ D)
    (hμ : 0<μ) (hz : μ≤1) (hw : σ ≤ μ*(1/128:ℝ)) (hσ : 0<σ) : ∀ i∈strip σ,(massif G μ T).tab i=dais G μ B i := by
  apply Poster.renew (massif_green hμ hz hw h).tab (dais_charge B hμ hz hσ hw hΩ) hσ he
  refine fun i => ⟨_,((grantM (hf i) hμ).tab),?_⟩; rw [cardM,input_zero]; exact daisy hμ p R B hX hF (hy i) (hB i) (B.metric.rights _ _ hΩ hσ.le)
end scope
end YM.Stationary
end

/-!
# Fixed mesh-independent strip. May depend on L.
on all cofinal meshes. Ticket identity local kernel determinant, no actual strip
 tilt on joint Hessian imported from that calculation. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {q : Momentum} {σ η A C D ε μ : ℝ} {m : Side} {n : ℕ}

lemma gardenGate {α : Type} [Fintype α] [DecidableEq α] {U : Momentum→CompM α α} (hs : 0<σ) (h : Poster σ U) (he : ∀ x,star x=x → IsUnit (U x).det) : ∃ τ, 0<τ ∧ τ ≤ σ ∧ ∀ p∈strip τ, IsUnit (U p).det := by
  let D := {i:Momentum| i∈strip σ ∧ (U i).det≠0}
  have hd : IsOpen D := by
    apply isOpen_iff_mem_nhds.mpr; intro p hp
    refine Filter.inter_mem ((Work.F07.stripOpen σ).mem_nhds hp.1) (((h.shape hp.1).via_det.continuousAt).eventually_ne hp.2)
  have hp : pier 0 ⊆ D := by
    intro p h'; have hx i := h'.2 i; refine ⟨fun i=> (hx i).trans_lt hs,(he _ ?_).ne_zero⟩; funext i; apply Complex.conj_eq_iff_im.mpr; exact abs_nonpos_iff.mp (hx i)
  obtain ⟨r,hr,hW⟩ := (pier_compact 0 le_rfl).exists_cthickening_subset_open hd hp
  refine ⟨min r σ,lt_min hr hs,min_le_right ..,fun i hi => ?_⟩
  obtain ⟨j,hj,hR⟩ := Nave.roll i
  have hh := skyPeriod hi hR.symm
  have hx : ground j ∈ pier 0 := ⟨fun i=> hj i,fun i=> by simp [ground,axes]⟩
  have hJ : dist j (ground j) ≤ r := by rw [dist_eq_norm]; exact (ground_near hh).le.trans (min_le_left ..)
  have ht := hW (Metric.mem_cthickening_of_dist_le _ _ _ _ hx hJ)
  exact (h.shifts hR ht.1) ▸ ht.2.isUnit

lemma luncheon (h : 0<σ) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {X : Film (Fslot G) α α} {Y : Film (Fslot G) β β} (hp : Play X σ) (hy : Play Y σ) (hx : ∀ p,star p=p → IsUnit (X.tab p).det) (he : ∀ p,star p=p → IsUnit (Y.tab p).det) :
    ∃ η A, 0<η ∧ 0≤A ∧ ∀ i j, Firm η A (starTrack ((((↑(1/2:ℝ)):ℂ) • X.figure-Y.figure) i j)) := by
  obtain ⟨a,ha,h1,A⟩ := gardenGate h hp.tab hx
  obtain ⟨b,hb,h2,B⟩ := gardenGate h hy.tab he
  let μ := min a b
  have hM : 0<μ := lt_min ha hb
  have hv : μ≤σ := (min_le_left ..).trans h1
  have hX i j := (hp.mono hv).estate hM (fun x hx=>A _ (fun k=> (hx k).trans_le (min_le_left ..))) i j
  have hY i j := (hy.mono hv).estate hM (fun x hx=> B _ (fun k=> (hx k).trans_le (min_le_right ..))) i j
  let η := μ/4
  have hh : 0<η := by unfold η; positivity
  have ht : η< μ/2 := by unfold η; linarith
  choose FX hf using fun i j=> calm_into (hX i j) hh ht
  choose GY hg using fun i j=> calm_into (hY i j) hh ht
  let c := (↑(1/2:ℝ):ℂ)
  let A i j := ‖c‖ * FX i j + GY i j
  have hZ i j : 0≤A i j := add_nonneg (mul_nonneg (norm_nonneg _) (hf .. |>.budget_nonneg)) (hg i j |>.budget_nonneg)
  refine ⟨η,∑ i,∑ j,A i j,hh,sum_nonneg (fun i _ => sum_nonneg (fun j _=>hZ i j)),fun i j=> ?_⟩
  exact ((((Firm.const hh c).mul (hf i j)).sub (hg i j)).mono hh le_rfl ((single_le_sum (s:=univ) (fun k _=> hZ i k) (mem_univ j)).trans (single_le_sum (s:=univ) (f:=fun i=>∑ j,A i j) (fun i _=>sum_nonneg fun j _=>hZ i j) (mem_univ i))))
structure HouseWord (G : Gauge) (B : Bed) (k : Clip) (D : ℝ) (ε : ℝ) (σ C μ : ℝ) (F : KindF G) : Prop where
    prog : Play F σ
    metric : B.metric.strip σ C
    amount : 0<μ ∧ μ≤1
    phase : σ≤μ*(1/128)
    pos : 0<σ
    pact : ∀ i∈strip σ,(massif G μ F).tab i=dais G μ B i
    lower : ∀ m, Floor B k m ε D
    positive : 0<ε
lemma HouseWord.done {B : Bed} {F : KindF G} (h : HouseWord G B p D ε σ C μ F) : ∃ η A : ℝ, 0<η ∧ 0≤A ∧ ∀ i j, Firm η A (starTrack (amena μ G F i j)) := by
  refine luncheon h.pos (X:=massif G μ F) (Y:=coring G μ) (massif_green h.amount.1 h.amount.2 h.phase h.prog) ((flake h.amount.1 h.amount.2).mono h.phase) (fun i hi=>?_) (fun i hi=>?_)
  · rw [h.pact i (Work.F07.realStrip _ h.pos hi)]
    exact (stable_real (fun x=> dais_floor hi p B h.amount.1 x h.metric h.pos h.lower h.positive)).safe (mul_pos (div_pos (lt_min h.positive zero_lt_one) (by norm_num)) (peb_pos i h.amount.1))
  rw [flakeTabs h.amount.1 h.amount.2 i (Work.F07.realStrip _ (h.pos.trans_le h.phase) hi)]
  exact (stable_real (fun x=> throne_floor x hi h.amount.1)).safe (mul_pos (by norm_num) (peb_pos i h.amount.1))
end YM.Stationary
end

/-!
# Station cost for thermal tilt in HorizCalc, choice over ages. Use
 width `B.metric` independent; note Wilson MOUNT attached not assumed.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {p : Clip} {R : PathData G} {n : ℕ} {m : ℕ → Side} {F : KindF G} {B : Bed} {σ τ η A C D Z ε μ : ℝ}
structure Jar (G : Gauge) where
    um : Picture G 1
    prim : Picture G 2
    trio : Picture G 3
variable {U : Jar G}
namespace Jar
def cast (U : Jar G) := vintage U.um U.prim U.trio
abbrev fees (U : Jar G) (σ M : ℝ) := (∀ i j,Firm σ M (U.um i j)) ∧ (∀ i j, Firm σ M (U.prim i j)) ∧ (∀ i j,Firm σ M (U.trio i j))
def bindV {c : Side} (U : Jar G) (F : Link G c→ℝ) := DrinkIt U.um F (creme 0) ∧ DrinkIt U.prim F (creme 1) ∧ DrinkIt U.trio F (creme 2)
def soft (U : Jar G) (u : ℕ) := (∀ i j,Rays u (U.um i j ∘ axes)) ∧ (∀ i j,Rays (u-1) (U.prim i j ∘ axes)) ∧ ∀ i j,Rays (u-2) (U.trio i j ∘ axes)

lemma fees.less (hv : fees U σ C) (he : 0<η) (ht : η≤σ) (hA : C≤A) : fees U η A := ⟨fun i j=> (hv.1 i j).mono he ht hA, fun i j=> (hv.2.1 i j).mono he ht hA, fun i j=> (hv.2.2 i j).mono he ht hA⟩
def combine (U V : Jar G) : Jar G := ⟨U.um+V.um,U.prim+V.prim,U.trio+V.trio⟩
lemma fees.pay {V : Jar G} (hv : fees U σ A) (he : fees V σ C) : fees (combine U V) σ (A+C) := ⟨fun i j=> (hv.1 i j).add (he.1 i j), fun i j=> (hv.2.1 i j).add (he.2.1 i j), fun i j=> (hv.2.2 i j).add (he.2.2 i j)⟩
lemma sequel {c : Side} {F H : Link G c→ℝ} (hF : AnalyticAt ℝ F 0) (hH : AnalyticAt ℝ H 0) {J L : Picture G n} {x : Breed n Bool} (h : DrinkIt J F x) (he : DrinkIt L H x) : DrinkIt (J+L) (F+H) x := by
  intro i b p; rw [labelAdd,← h,← he]
  unfold liquid; rw [show (F+H) ∘ dough G c=F ∘ dough G c + H ∘ dough G c from rfl,beat_as_cost, note_add ?_ ?_,smul_add,← beat_as_cost,← beat_as_cost]; pick_goal 2
  exact AnalyticAt.comp (f:=dough G c) (by rw [dough_zero]; exact hF) (dough_floats ..)
  pick_goal 2
  exact AnalyticAt.comp (f:=dough G c) (by rw [dough_zero]; exact hH) (dough_floats ..)
  rfl
lemma sequelQ {c : Side} {V : Jar G} {F H : Link G c→ℝ} (hF : AnalyticAt ℝ F 0) (hH : AnalyticAt ℝ H 0) (h : bindV U F) (he : bindV V H) : bindV (combine U V) (F+H) := ⟨sequel hF hH h.1 he.1,sequel hF hH h.2.1 he.2.1,sequel hF hH h.2.2 he.2.2⟩
lemma cast_book (h : fees U σ A) (i : Side) (he : bindV U (intended p R (m:=i))) (hp : R.Bounds p τ D C) : Ticket U.cast (fineFlare p R (m:=i)) := epic h.1 h.2.1 h.2.2 hp he.1 he.2.1 he.2.2
lemma fees.live (h : fees U σ A) : Play U.cast σ := wine_play _ _ _ h.1 h.2.1 h.2.2
end Jar

def Jar.grey (U : Jar G) := ∀ i : Side, U.bindV (WilsonQ G i)

lemma jig (hs : 0<σ) (hA : 0≤A) (n : ℕ) : ∃ η M,0<η ∧ 0≤M ∧ ∀ (m : ℕ→Side) (U : ∀ i,Link G (m i)→ℝ), (∀ i, AnalyticAt ℝ (U i) 0) → (∀ i, fderiv ℝ (U i) 0=0) → (∀ i, i>0 → i≤3 → Drinkable i m U (n-(i-1)) σ A) →
    ∃ K : Jar G, K.fees η M ∧ K.soft n ∧ ∀ i, K.bindV (U i) := by
  let u k := calls (k+1) σ
  have hu k : 0<u k := by unfold u calls; positivity
  let τ := min (u 1) (min (u 2) (u 3)); have hT : 0<τ := lt_min (hu 1) (lt_min (hu 2) (hu 3))
  let a (i : ℕ) := A*pintCost (creme i) G; let X := max (max (a 0) (a 1)) (a 2)
  refine ⟨τ,max 0 X,hT,le_max_left ..,fun m U hy he hf => ?_⟩
  have hk (i) (hi : i≤2) : ∃ H : Picture G (i+1), (∀ j,DrinkIt H (U j) (creme i)) ∧ ∀ p q, Firm (u (i+1)) (a i) (H p q) ∧ Rays (n-i) (H p q ∘ axes) :=
    wedlock (m:=m) U (fun p hp hw => (hf p hp (by omega)).thins hs le_rfl le_rfl (by omega)) he (u:=n-i) (v:=creme i) hy hs hA
  obtain ⟨H,V,hv⟩ := hk 0 (by decide); obtain ⟨B,T,hb⟩ := hk 1 (by decide); obtain ⟨W,E,hE⟩ := hk 2 le_rfl
  refine ⟨⟨H,B,W⟩,⟨fun i j=> (hv i j).1.mono hT (min_le_left ..) (((le_max_left ..).trans (le_max_left ..)).trans (le_max_right 0 X)),fun i j=> (hb i j).1.mono hT ((min_le_right ..).trans (min_le_left ..)) (((le_max_right ..).trans (le_max_left ..)).trans (le_max_right _ X)),fun i j=> (hE i j).1.mono hT ((min_le_right ..).trans (min_le_right ..)) ((le_max_right ..).trans (le_max_right 0 X))⟩,
             ⟨fun i j=> (hv i j).2, fun i j=> (hb i j).2, fun i j=> (hE i j).2⟩,fun i=> ⟨V i,T i,E i⟩⟩

lemma vintageWilson (G : Gauge) : ∃ σ M,0<σ ∧ 0≤M ∧ ∃ U : Jar G, U.fees σ M ∧ U.grey := by
  obtain ⟨hf,A,hA,K,h,hL⟩ := Wilson_stream G 1
  obtain ⟨_,B,hB,F,ht,hF⟩ := Wilson_stream G 2
  obtain ⟨_,C,hC,L,hx,hx'⟩ := Wilson_stream G 3
  let m := walent
  let M := A+B+C
  have hM : 0 ≤ M := add_nonneg (add_nonneg hA hB) hC
  obtain ⟨τ,N,hτ,hN,Q⟩ := jig (G:=G) zero_lt_one hM 0
  obtain ⟨X,hX,hY,H⟩ := Q m (fun i=>WilsonQ G (m i)) (fun i=> hf _) (fun i=> (outright G (m i)).2.1) (fun i hi hk=> by
    interval_cases i
    · exact ⟨_,fun i=>hL _,fun i j=> ⟨(h i j).mono zero_lt_one le_rfl (by unfold M; linarith),rays_zero ((h _ _).analytic_real 0)⟩⟩
    · exact ⟨_,fun i=> hF _, fun i j=> ⟨(ht i j).mono zero_lt_one le_rfl (by unfold M; linarith),rays_zero ((ht _ _).analytic_real 0)⟩⟩
    exact ⟨_,fun i=> hx' _, fun i j=> ⟨(hx i j).mono zero_lt_one le_rfl (by unfold M; linarith),rays_zero ((hx _ _).analytic_real 0)⟩⟩)
  refine ⟨τ,N,hτ,hN,X,hX, fun i=> ?_⟩
  rcases i with ⟨i,h⟩; cases i with
  | zero => omega
  | succ i => exact H i

lemma saunter (G : Gauge) (hG : G.Simple) (σ ε C Z τ A : ℝ) (hs : 0<σ) (hC : 0≤C) (hZ : 0≤Z) (ht : 0<τ) (hA : 0≤A) : ∃ w K,0<w ∧ 0≤K ∧ ∀ (m : ℕ→Side), Tendsto (fun i=> (m i).val) atTop atTop → ∀ (B : Bed) (p : Clip) (R : PathData G) (Λ : ℝ), R.Bounds p τ A Λ → Attached B R → B.metric.strip σ C → p.direct≤Z → (∀ n, Floor B p n ε C) → (∀ i,Bid.Sworn B (m i) G) →
    ∃ U : Jar G,U.fees w K ∧ U.soft 3 ∧ ∀ i,U.bindV (intended p R-WilsonQ G (m i)) := by
  obtain ⟨k,M,hk,hM,H⟩ := greyson G σ ε C Z τ A hs hC hZ ht hA
  obtain ⟨w,K,hw,hx,L⟩ := jig (G:=G) hk hM 3
  refine ⟨w,K,hw,hx,fun m hm B p R Λ h hp hz he hh hv => ?_⟩
  refine L m (fun i=> intended p R-WilsonQ G (m i)) (fun i=> (strain _ _ h).analytic.sub ((Wilson_stream _ 2).1 _)) (fun i=> ?_) (fun i hi hZ'=> ?_)
  · rw [fderiv_sub (strain _ _ h).analytic.differentiableAt ((Wilson_stream G 2).1 _).differentiableAt, pact h hp (fun i=> hh (m i)) hv i,(outright G (m i)).2.1,sub_self]
  rw [show 3-(_-1)=4-i by omega]; exact H m hm B p R Λ h hp hz he hh hv i hi hZ'
end YM.Stationary
end
