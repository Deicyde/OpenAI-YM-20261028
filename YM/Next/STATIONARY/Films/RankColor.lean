import YM.Next.STATIONARY.Films.TraceDifference

set_option autoImplicit false
/-!
# Choose convergence widths without knowing kinetic inputs at a later level.
 wp draws modal charge at THESE prices from orbit factories. No packed
across m without same Q. Values are in true contour sets. α drift not used
here. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : Gauge} {P : Patch} {K : KernelChoices} {σ A C D η : ℝ} {c f : Side}

structure GrantF (P : Patch) (r : KernelChoices) (E : Eye ι (Acts G P)) (U : Spark ι G P) (B : Bed) (σ C : ℝ) : Prop where
  ranking : Freezer (altarTile _ _ |>.dual) (altarTile _ _) (rankF E U).tab σ C
  copy : Freezer (slabW G P.L|>.dual) (slabW G P.L) (rankUpF E U).tab σ C
  medals : Freezer (slabW G P.L|>.dual) (slabW G P.L) (medalF E false U r.penalty).tab σ C
  core : Freezer (slabW G P.L|>.dual) (slabW G P.L) (legionF E false U r.penalty).tab σ C
  grenade : Freezer (altarTile _ _|>.dual) (altarTile _ _) (grenadeFilm E).tab σ C
  ranks : ColdRank G P B σ C
  tones : ColdTone G P σ C
-- Use theorem only with staged P. Later alpha gets Coy. Does not certify portrait Req for missing RShape!

theorem honored (G : Gauge) (r : KernelChoices) (J : ℕ) (σ ε Θ A : ℝ) (he : 0<ε) (hp : 0<σ) (ht : 0≤Θ) (hv : 0≤ A) :
    ∃ w η C D : ℝ, 0<η ∧ η ≤ w ∧ w ≤ σ ∧ w ≤ 1/128 ∧ 0≤C ∧ 0≤D ∧
      (∀ L : Side, Amateur G L w C) ∧
      ∀ (P : Patch), P.J=J → P.Branches r G → ∀ (p : Clip) (R : PathData G) (m n : ℕ→Side) (T : Type) [Fintype T] [DecidableEq T] (E : Eye T (Acts G P)) (X : Spark T G P)
        (H : Bed) (Q : PostCard R p P r E X m n),
         Tendsto (fun i => (m i).val) atTop atTop → ∀ τ Ω β B D₀ : ℝ, R.Bounds p τ Ω β →
          Attached H R → H.metric.strip (inch P.L*w) Θ → (∀ i, Floor H p i ε D₀) → (∀ i, Bid.Sworn H (n i) G) →
          Spotlight P E w A → Keels X w B → GrantF P r E X H η D := by
  obtain ⟨z,C,hz,hz₀,hC,Gc⟩ := amasses G
  obtain ⟨v,B,hb,hv₀,hB,hT⟩ := chillThrone G
  let w := min σ (min v z)
  have hw : 0<w := lt_min hp (lt_min hb hz)
  have hh : w≤v := (min_le_right ..).trans (min_le_left ..)
  have hH : w≤z := (min_le_right ..).trans (min_le_right ..)
  have hr : w≤1/128 := hh.trans hv₀
  have hc : w≤1 := by linarith
  obtain ⟨e,V,ha,hp',hG,T⟩ := post_cert G J r ε w Θ |tribute2 G J A C| he hw hc ht (abs_nonneg _)
  obtain ⟨l,W,hu,hy,hW,H⟩ := chillDais G hw hr ht he
  let η := min e l
  let D := max W 1+V+B
  have hη : 0<η := lt_min ha hu
  have hX : η ≤ w := (min_le_left ..).trans hp'
  have hA : 0 < max W 1 := lt_of_lt_of_le zero_lt_one (le_max_right W 1)
  have hD : 0≤D := by unfold D; positivity
  refine ⟨w,η,C,D,hη,hX,min_le_left ..,hr,hC,hD,fun L => Gc L w hH,?_⟩
  intro P hP hs p R m n I _ _ E X Vb Q hm τ Ω β B' D₀ hu' heH hK hF hi hE hY
  have hx : Amateur G P.L w C := Gc _ w hH
  have heV := legion_right hs hw hE hx X hY
  have hc' := conquer hs hw hE hx
  have hp'' := rankRight hw hE hx X hY
  have hCold : ColdRank G P Vb l W := H P.L Vb p _ hK hF
  have hf := freezeRank Q hs hm ((show Charges _ _ _ _ _ from hp'').covered) hw hr hu' heH hK (fun i=>hF _) hi hy hCold
  have ht₀ := rankUpFreeze hf
  have hX := hc'.covered.tab
  have ht := T P hP hs Vb _ _ (CanonR E false).tab m n Q.ship hm hK hF hX (fun p w => (hc'.base w).mono (by rw [← hP]; exact le_abs_self _)) Q.tags (meterMark Q hs)
  have hd := absoluteTone (E:=E) (P:=P) (show ColdTone G P w B from (hT _).mono hh le_rfl) hr
  have hy := freezeLegion Q hs hm heV hX hw hu' heH hK (fun i=>hF _) hi hp' ht
  have hz := freezeMedal Q hs hm (medals_right hs hw hE hx X hY) hX hw hu' heH hK (fun i=>hF _) hi hp' ht
  have hv : max W 1 ≤ D := by unfold D; linarith
  have hWl : W ≤ D := (le_max_left ..).trans hv
  have hk : V≤ D := by unfold D; linarith
  have hL : B≤D := by unfold D; linarith
  refine ⟨hf.mono (min_le_right ..) hWl,ht₀.mono (min_le_right ..) hv,hz.mono (min_le_left ..) hk, hy.mono (min_le_left ..) hk,hd.mono ‹η≤w› hL,
    Freezer.mono hCold (min_le_right ..) hWl, Freezer.mono (hT _) (le_trans ‹η≤w› hh) hL⟩
end YM.Stationary
end

/-!
# On the merit comparison actual awards. `Spout` on voter-present mesh, Γ
 subtract only once. α still from Π-drift after relative rank comparison.
-/
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {p : Clip} {R : PathData G} {σ τ A C D Λ E γ : ℝ} {c f L : Side}
section all
variable (D : Eye (Loc G 1) (Acts G P)) (k : ℝ) (X : Spark (Loc G 1) G P)
def medalCue := ((↑(1/2:ℝ)):ℂ) • (medalF D false X k).figure-(grenadeFilm D).figure
def rankCue := ((↑(1/2:ℝ)):ℂ) • (rankUpF D X).figure-(grenadeFilm D).figure
def coreCue := ((↑(1/2:ℝ)):ℂ) • (legionF D false X k).figure-(grenadeFilm D).figure
def changeCue := medalCue D k X-coreCue D k X
def stageCue := coreCue D k X-rankCue D X
end all
variable (S : StepData c f) (t : S.Choices)
def upperCore (p : Clip) (R : PathData G) (x : Point G c f) := (1/2:ℝ)*coreBoon S t p R (inch S.patch.L) x - Real.log (grenade (inch S.patch.L) (Stationary.extend x.2).1).det
def cardHand (W : Matrix (Body 1 f) (Body 1 c) ℝ) : Link G c →L[ℝ] Bang G c f := (saluteLe (G:=G) W).prod 0

section audience
variable {α β a b : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {f : Film (Loc G 1) a a} {g : Film (Loc G 1) b b}
-- fold. Functions on actual mesh.
lemma ring_award (T : α≃ Co c a) (Y : β≃ Co c b) {A : Link G c → Funds α} {B : Link G c →Funds β} (h : Ticket f (fun x => repackM T T (A x))) (hp : Ticket g (fun x=> repackM Y Y (B x))) (hv : IsUnit (A 0).det) (hx : IsUnit (B 0).det) :
    Awards (((↑(1/2:ℝ)):ℂ) • f.figure-g.figure) ((1/2:ℝ) • (fun z => Real.log (A z).det)-(fun z => Real.log (B z).det)) := by
  let M := fun z => Real.log (repackM T T (A z)).det
  let N := fun z => Real.log (repackM Y Y (B z)).det
  have hv : IsUnit (repackM T T (A 0)).det := by rw [repack_det]; exact hv
  have hx : IsUnit (repackM Y Y (B 0)).det := by rw [repack_det]; exact hx
  have he : AnalyticAt ℝ M 0 := ((Memo.det_val h.finance).log hv.ne_zero).analyticAt
  have hu : AnalyticAt ℝ N 0 := ((Memo.det_val hp.finance).log hx.ne_zero).analyticAt
  have ht := (Awards.rebate (f:=f.figure) (P:=M) (h.award hv) he (1/2)).less (g:=g.figure) (Q:=N) (hp.award hx) (AnalyticAt.const_smul he) hu
  unfold M N at ht; simp_rw [repack_det] at ht; exact ht
end audience
section issue
variable {F : Forest S.ratio} {ρ} {Q : Bed} (h : Critical F p R ρ)
    (hc : R.Bounds p σ A Λ) (hQ : Attached Q R) (hX : Floor Q p f τ D) (hI : Bid.Sworn Q f G) (hv : PriceGap F p R γ) (hz : 0<γ) (hp : S.patch.Branches S.kernel G)
    (W : Matrix (Body 1 f) (Body 1 c) ℝ) (hw : Guessed F W ρ)
    {X : Spark (Loc G 1) G S.patch} {M : Eye (Loc G 1) (Acts G S.patch)} (H : Turns M (atlasQ S W))
    (HK : Ticket X (fun x => repackM (unitSplit G S 1) (unitSplit G S 1) (flare p R (input G f (uniformM (G:=G) W x)))))
include h hc hp hz hv H HK
lemma questBright (hG : G.Simple) (hw : Guessed F W ρ) : Awards (medalCue M S.kernel.penalty X) (honorarium F t (inch S.patch.L) p R ρ) := by
  classical
  let J := cardHand (G:=G) W
  let T := clothe G S; let Y : Lines G f 0 ≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  let μ := inch S.patch.L
  let U x := Stationary.extend (endorse (G:=G) W x)
  let H₁ x := medals S t p R μ (fedora S t) (input G c x) (U x)
  let K x := grenade μ (U x).1
  let a x : ℝ := Real.log (H₁ x).det
  let b x : ℝ := Real.log (K x).det
  have hL : Ticket (medalF M false X S.kernel.penalty) (fun x => repackM T T (H₁ x)) := rewarded S hp t false J hc (fun _=>rfl) H HK
  have hK : Ticket (grenadeFilm M) (fun x => repackM Y Y (K x)) := shipGren S t false J H
  have hu : U 0=1 := by unfold U; rw [map_zero, extend_zero]
  have hU : IsUnit (H₁ 0).det := by unfold H₁; rw [hu,input_zero]; exact (moment_track h hp hc t (inch_pos _) hv hz).1.ne'.isUnit
  have hg : IsUnit (K 0).det := by exact fund_det (grenade_safe _ (inch_pos _))
  have HH := ring_award T Y (A:=H₁) (B:=K) (f:=medalF M false X S.kernel.penalty) (g:=grenadeFilm M) hL hK hU hg
  apply HH.carry (show _ from ?_)
  change iteratedFDeriv ℝ 2 (honorarium F t μ p R ρ) _=_
  rw [elect h hp hc t (inch_pos _) hG W hw hv hz]; rfl
lemma questCore :
    Awards (coreCue M S.kernel.penalty X) (upperCore S t p R ∘ saluteLe (G:=G) W) := by
  classical
  let J := cardHand (G:=G) W
  let T := clothe G S; let Y : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  let μ := inch S.patch.L
  let U x := Stationary.extend (endorse (G:=G) W x)
  let A x := legion S t p R μ (fedora S t) (input G c x) (U x)
  let B x := grenade μ (U x).1
  have he : Ticket (legionF M false X S.kernel.penalty) (fun x => repackM T T (A x)) := legislature S t false J H hp (fun _=>rfl) (fun _=>rfl) HK
  have hb : Ticket (grenadeFilm M) (fun x => repackM Y Y (B x)) := shipGren S t false J H
  have hu : U 0=1 := by unfold U; rw [map_zero, extend_zero]
  have hU : IsUnit (A 0).det := by unfold A; rw [hu,input_zero,legion_origin hp hc t _ (fedora_style hp t)]; exact (moment_track h hp hc t (inch_pos _) hv hz).1.ne'.isUnit
  have hg : IsUnit (B 0).det := by exact fund_det (grenade_safe _ (inch_pos _))
  have HH := ring_award T Y (A:=A) (B:=B) (f:=legionF M false X S.kernel.penalty) (g:=grenadeFilm M) he hb hU hg; exact HH
include t hQ hX hI
omit h hz hv hp in
lemma questPole : Awards (rankCue M X) ((PoleTest p R (inch S.patch.L))∘ (uniformM (G:=G) W)) := by
  classical
  let J := cardHand (G:=G) W
  let T := clothe G S; let Y : Lines G f 0≃ Co c (Co S.patch.L (Loc G 0)) := unitSplit G S 0
  let μ := inch S.patch.L
  let U x := input G f (uniformM W x : Link G f)
  let K x := grenade μ (U x)
  let L x := rankUp G S p R (U x)
  have hb : Ticket (grenadeFilm M) (fun x => repackM Y Y (K x)) := shipGren S t false J H
  have hr : Ticket (rankUpF M X) (fun x => repackM T T (L x)) := rank_up_ticket S t false J H HK
  have hu : U 0=1 := by unfold U; rw [map_zero,input_zero]
  have hm : IsUnit (rankAux (1:Config G f) p R μ).det := fund_det (rank_positive μ hc hX hQ hI (inch_pos _))
  have hU : IsUnit (L 0).det := by unfold L; rw [headquarters, hu]; exact hm
  have hg : IsUnit (K 0).det := by exact fund_det (grenade_safe _ (inch_pos _))
  have HH := ring_award T Y (A:=L) (B:=K) (f:=rankUpF M X) (g:=grenadeFilm M) hr hb hU hg
  unfold L at HH; simp_rw [headquarters S] at HH; exact HH
end issue
end YM.Stationary
end

/-!
# Pre-L harmonic bills for the thermal trace. Includes a genuinely
volume-free relative rank signal. Uses thickness card EXACT; C on rank
may itself have depended on phase conv budgets. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset Tree
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {p : Clip} {R : PathData G} {σ τ A C D Λ F Ω η γ : ℝ} {c f L : Side}
section budget
-- all charges combined abs. Freezes GrantF at η. Price calculator includes D drift separately. Later X ≤... and consume. Λ only trace Hess inherited externally.

def granPay (G : Gauge) (j : ℕ) (C D : ℝ) := tonPay G j C+Real.exp 4*mealCa G j C D*Real.exp 4
def mealCap (G : Gauge) (j : ℕ) (C D A k : ℝ) := |legPay G j C D k A|+|boomPay G j C D k A|+|statusP G j C D A|+|granPay G j C D|

def tapeCost (G : Gauge) (F x : ℝ) := (((Fintype.card (Loc G 0)+Fintype.card (Loc G 1):ℕ):ℝ))*(F*x+F*x*F*x)
def reserveCost (G : Gauge) (F x k : ℝ) := let D := F*k*F; let E := D*x+F*k; E + ((E*F+F*x*D)*x + F*x*F*k)

structure Screened (M : Award G) (σ A : ℝ) : Prop where earns i j : Firm σ A (starTrack (M i j))
lemma Screened.bound {p q : Award G} (h : Screened p σ C) (hp : Screened q σ D) : Screened (p-q) σ (C+D) := ⟨fun i j => (h.earns _ _).sub (hp.earns _ _)⟩
lemma Screened.slight {p : Award G} (h : Screened p σ C) : Screened (((↑(1/2:ℝ)):ℂ) • p) σ C := by
  refine ⟨fun i j => ?_⟩; have he := h.earns i j
  let z : ℂ := ↑(1/2:ℝ)
  exact ((Firm.const he.width_pos z).mul he).mono he.width_pos le_rfl (mul_le_of_le_one_left he.budget_nonneg (by norm_num [z]))
lemma seats_area (L : Side) : Fintype.card (ParcelG G L) ≤ L.val^4 * (Fintype.card (Loc G 0) + Fintype.card (Loc G 1)) := by
  have he := site_card L
  have hy : 1 ≤ L.val^4 := one_le_pow₀ L.pos
  rw [Fintype.card_sum,Fintype.card_prod, Lattice.site_card,mul_add,add_comm (L.val^4*Fintype.card (Loc G 0))]; exact add_le_add_right (Nat.le_mul_of_pos_left _ hy) _
lemma paneCharge {α : Type} [Fintype α] [DecidableEq α] {X Y : Slab α} {M : Film (Loc G 1) α α} (h : Charges X Y M η A) (hp : Freezer X Y M.tab η F) (he : 0<η) (hk : 0≤F)
    (hz : Fintype.card α ≤ L.val^4 * (Fintype.card (Loc G 0) + Fintype.card (Loc G 1))) : Screened M.figure (η/2) ((L.val:ℝ)^4*tapeCost G F A) := by
  have ht := h.funds he
  refine ⟨fun i j => (Freezer.figure h hp he i j).mono (by positivity) le_rfl ?_⟩
  unfold tapeCost; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hz) (by positivity)

lemma gifts_real {X : Spark (Loc G 1) G P} {M : Eye (Loc G 1) (Acts G P)} (p : P.Branches K G) (h : Spotlight P M σ C) (hk : σ≤1/128)
    (he : 0<η) (hp : η≤σ) (hx : Amateur G P.L σ D) (hv : Keels X σ A)
    {B : Bed} (hu : GrantF P K M X B η F) (hy : 0≤F) :
    let i := P.J
    let Γ := mealCap G i C D A K.penalty
    let Q := (P.L.val:ℝ)^4*tapeCost G F Γ
    Screened (medalCue M K.penalty X) (η/2) (Q+Q) ∧
    Screened (coreCue M K.penalty X) (η/2) (Q+Q) ∧
    Screened (rankCue M X) (η/2) (Q+Q) ∧
    Screened (stageCue M K.penalty X) (η/2) (reserveCost G F Γ (barkPay G P.J C D K.penalty)) := by
  intro i Γ Q
  have hσ := he.trans_le hp
  let H := (medals_right p hσ h hx X hv)
  let L := (legion_right p hσ h hx X hv)
  let T := rankUpRight hσ h hx X hv
  let U := gran_frozen h hσ hx
  let F₁ := medalF M false X K.penalty; let F₂ := legionF M false X K.penalty; let F₃ := rankUpF M X
  let Z := slabW G P.L
  have HA := H.funds hσ; have HB := L.funds hσ; have HC := T.funds hσ; have HD : 0≤ granPay G P.J C D := U.funds hσ
  have hB : Charges Z.dual Z F₂ η Γ := L.mono hp (by unfold Γ i mealCap; rw [abs_of_nonneg HB]; linarith [abs_nonneg (boomPay G P.J C D K.penalty A),abs_nonneg (statusP G P.J C D A),abs_nonneg (granPay G P.J C D)])
  have hT : Charges Z.dual Z F₃ η Γ := T.mono hp (by unfold Γ i mealCap; rw [abs_of_nonneg HA,abs_of_nonneg HB,abs_of_nonneg HC,abs_of_nonneg HD]; linarith)
  have hM : Screened (grenadeFilm M).figure (η/2) Q := paneCharge (U.mono hp (by
    change granPay G P.J C D≤Γ; unfold Γ mealCap i; rw [abs_of_nonneg HA,abs_of_nonneg HB,abs_of_nonneg HC,abs_of_nonneg HD]; linarith)) hu.grenade he hy (by
    rw [Fintype.card_prod, site_card]; gcongr; omega)
  have hl : Screened F₁.figure (η/2) Q := paneCharge (H.mono hp (by
    unfold Γ mealCap i; rw [abs_of_nonneg HA,abs_of_nonneg HB,abs_of_nonneg HC,abs_of_nonneg HD]; linarith)) hu.medals he hy (seats_area P.L)
  refine ⟨hl.slight.bound hM, (Screened.slight (paneCharge hB hu.core he hy (seats_area P.L))).bound hM, (Screened.slight (paneCharge hT hu.copy he hy (seats_area P.L))).bound hM,?_⟩
  have hr := (full_tolls h hσ hx hk p X).mono hp le_rfl
  let k := barkPay G P.J C D K.penalty
  have hh : Screened ((legionF M false X K.penalty).figure-(rankUpF M X).figure) (η/2) (reserveCost G F Γ k) := ⟨fun i j => ledger_cmp hB hT hu.core hu.copy he hr i j⟩
  rw [stageCue,coreCue,rankCue,sub_sub_sub_cancel_right, ← smul_sub]; exact hh.slight
end budget
end YM.Stationary
end
