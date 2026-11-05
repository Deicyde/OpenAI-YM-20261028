import YM.Next.STATIONARY.FrameEst.Center



set_option autoImplicit false
/-!
# Supported probability accounts on one (enlarged) patch. Applies leg-length
and tile payments. After observing connector-to-step all heights still use
same P.L. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α : Type} [Fintype α] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : Gauge} {P : Patch} {n k m : ℕ} {R : X→ℕ→Prop} {K : KernelChoices} {C : ℝ} {U : X→CoverConfig G}

def playhouse (P : Patch) := box ((P.J+5)*P.L.val)
abbrev Plaza (P : Patch) := ↥(playhouse P)
instance : Nonempty (Plaza P) := ⟨⟨0,center_box _⟩⟩
lemma alley (i : P.Points) : i.val∈playhouse P := by simpa only [zero_smul,add_zero,playhouse] using rent_fit P i 0 0 (Nat.zero_le _)
lemma alley_pin (P : Patch) : (P.L.val:ℝ)^4 ≤ Fintype.card P.Points := by
  have he (x : P.Small) : x.val∈P.sites := by
    have hz := x.property; obtain ⟨ha,hv⟩ := box_test.mp hz
    have hk : P.L.val/2 ≤ P.radius := Nat.le_trans (Nat.div_le_self ..) (Nat.le_mul_of_pos_left _ (by omega))
    exact box_test.mpr ⟨fun i => (neg_le_neg (by exact_mod_cast hk)).trans (ha i), fun i => (hv i).trans (by exact_mod_cast hk)⟩
  have ht : P.L.val^4 ≤ Fintype.card P.Points := by rw [← roll_card P]; exact Fintype.card_le_of_injective (fun i : P.Small => (⟨i.val,he i⟩ : P.Points)) (fun x y h => Subtype.ext (congrArg (fun i : P.Points => i.val) h))
  exact_mod_cast ht
lemma alley_admissions (P : Patch) : Fintype.card (Plaza P) ≤ portrait (P.J+2)*(P.L.val:ℝ)^4 := by
  change (Fintype.card ↥(box _):ℝ) ≤ _; rw [portrait_card,portrait, ← mul_pow]; push_cast; apply pow_le_pow_left₀ (by positivity)
  have h : 1 ≤ (P.L.val:ℝ) := by exact_mod_cast P.L.pos
  linarith
lemma alley_pass (i : P.Points) (j : Plaza P) : (balcony P.Points).weight i ≤ portrait (P.J+2)*(balcony (Plaza P)).weight j := by
  have he : 0 < (Fintype.card (Plaza P):ℝ) := by exact_mod_cast Fintype.card_pos
  have hu : 0 < (Fintype.card P.Points:ℝ) := by exact_mod_cast Fintype.card_pos
  change _⁻¹ ≤ _ * (Fintype.card (Plaza P):ℝ)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ he, inv_mul_eq_div, div_le_iff₀ hu]
  exact (alley_admissions P).trans (mul_le_mul_of_nonneg_left (alley_pin P) (zero_le_one.trans (painted _)))

-- permission on true sites with padded window. No powers in star reads.
def Sung (P : Patch) (R : X→ℕ→Prop) (U : X→CoverConfig G) (m : ℕ) (C : ℝ) := ∀ i : Axis,Gallop (balcony (Plaza P)) R (fun v x => G.mat (U x (v.val,i))) m (inch P.L*C)
lemma Sung.marks (h : Sung P R U m C) (x : Cover) (i : Axis) (hp : ∀ v : P.Points,v.val+x∈playhouse P) : Gallop (balcony P.Points) R (fun v z => G.mat (U z (v.val+x,i))) m (inch P.L*(portrait (P.J+2)*C)) := by
  rw [mul_left_comm, show portrait _*(inch P.L*C)=_ from rfl]
  let a (v : P.Points) : Plaza P := ⟨v.val+x,hp v⟩
  exact (h i).moveFast (s:=univ) (painted _) a (fun u _ v _ h => Subtype.ext (add_right_cancel (b:=x) (congrArg (fun i : Plaza P => i.val) h))) (fun i _ => ⟨rfl,alley_pass i _⟩) (by simp)
lemma Sung.stepUp (h : Sung P R U m C) (i : Axis) : Singer P R (fun z => translate (P.L.val • step i) (U z)) m (portrait (P.J+2) * C) := fun b => h.marks (P.L.val • step i) b (fun x => rent_fit P x i _ le_rfl)
lemma Sung.lower (h : Sung P R U m C) : Singer P R U m (portrait (P.J+2)* C) := by
  intro i; simpa only [add_zero] using h.marks 0 i (fun x => by rw [add_zero]; exact alley x)

def roadmap (P : Patch) (U : CoverConfig G) (v : P.Points) (i : Axis) (k : ℕ) := travel U v.val (List.replicate k (posDir i))
lemma roadmap_steps (U : CoverConfig G) (v : P.Points) (i : Axis) (k : ℕ) : roadmap P U v i (k+1)=roadmap P U v i k*U (v.val+k • step i,i) := by
  unfold roadmap; rw [List.replicate_add,travel_append,stop_prongs]; simp [travel]
lemma crossing_stamp (h : Sung P R U m C) (hp : U 0=1) (i : Axis) :
    Gallop (balcony P.Points) R (fun v x => G.mat (roadmap P (U x) v i P.L.val)) m (convoy G.Mat 1 (portrait (P.J+2)*C) m) := by
  let p := fun k (v : P.Points) x => G.mat (roadmap P (U x) v i k)
  let F := fun (k : ℕ) (v : P.Points) x => G.mat (U x (v.val+k • step i,i))
  have he k : p (k+1)=fun i x => p k i x* F k i x := by funext v x; unfold p F; rw [roadmap_steps,G.mat_mul]
  have hk : 0≤C := nonneg_of_mul_nonneg_right (h i).stamp (inch_pos _)
  apply convoyed p F (m:=P.L.val) (fun k _ => he k) (by simp [F,hp]) (by intros i; funext v; simp [p,roadmap,travel]) (mul_nonneg (zero_le_one.trans (painted _)) hk) (inch_pos _) (by rw [mul_comm,inch_unit]) (fun j hj => h.marks _ _ (fun v => rent_fit P v i j hj.le)) _ le_rfl
lemma crossing_local {U V : CoverConfig G} (v : P.Points) (i : Axis) (p : ∀ j ∈ playhouse P, ∀ i, U (j,i)=V (j,i)) (k : ℕ) (h : k≤P.L.val) : roadmap P U v i k=roadmap P V v i k := by
  induction k with
  | zero => simp [roadmap,travel]
  | succ k ih => rw [roadmap_steps,roadmap_steps,ih (by omega),p _ (rent_fit P v i k (by omega)) i]
end YM.Stationary
end

/-!
# Canonical connector lens. Frame recentered. Itinerary uses ONE shared tag
history. Local equality near each origin simultaneously. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α : Type} [Fintype α] {c f : Side} (S : StepData c f) {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : Gauge} {P : Patch} {n k m : ℕ} {R : X→ℕ→Prop} {K : KernelChoices} {C : ℝ} {U T : X→CoverConfig G} {V : X→Config G f}

-- centered Y at cover patch of head. root-mode looks different!
def hall (P : Patch) (U : CoverConfig G) (i : Axis) := translate (P.L.val • step i) U
lemma hall_one (P : Patch) (i : Axis) : hall P (1:CoverConfig G) i=1 := by funext z; rfl
lemma hallUp (h : Army U 0) (P : Patch) (i : Axis) : Army (fun x => hall P (U x) i) 0 := fun v => h _
lemma house_moves (U : Config G f) (a : Site c) (i : Axis) : hall S.patch (expandAt (S.ratio.embed a) U) i=expandAt (S.ratio.embed (a+step i)) U := by
  ext1 v; simp only [hall, expandAt, translate,map_add,map_nsmul,S.leap,wrap_step]; rw [add_right_comm,add_assoc]

def agora (P : Patch) (U : CoverConfig G) (v : P.Points) (i : Axis) := choirCap P U v * roadmap P U v i P.L.val * (choirCap P (hall P U i) v)⁻¹
def litBox (P : Patch) (U : CoverConfig G) (i : Axis) := (salon P).partakes (fun v => G.mat (agora P U v i))
def victoryBox (P : Patch) (U : CoverConfig G) (i : Axis) := G.focus (litBox P U i)
lemma agora_zero (h : P.Branches K G) (v : P.Points) (i) : agora P (1:CoverConfig G) v i=1 := by simp [agora,hall_one, cap_ground h,roadmap,Pressure.one]
lemma lit_ground (h : P.Branches K G) (i) : litBox P (1:CoverConfig G) i=1 := by simp [litBox,agora_zero h]
lemma victory_box0 (h : P.Branches K G) (i) : victoryBox P (1:CoverConfig G) i=1 := by rw [victoryBox,lit_ground h,focus_zero]

def canopyFare (G : Gauge) (j m : ℕ) (C : ℝ) := let a := portrait (j+2)*C; let c := subbass G j a m; let w := convoy G.Mat 1 a m; choirSquare G (choirSquare G c w 1 1 m) c 1 1 m
lemma agora_fare (i : Axis) (h : P.Branches K G) (p : Army U 0) (hp : U 0=1) (he : Sung P R U m C) :
    Gallop (balcony P.Points) R (fun j x => G.mat (agora P (U x) j i)) m (canopyFare G P.J m C) := by
  let T x := hall P (U x) i
  have ht : Army T 0 := hallUp p P i
  have hu : T 0=1 := by simp only [T,hp,hall_one]
  have hb : Singer P R T m _ := he.stepUp i
  have hh := Gallop.notes_star G (pre_choir h ht hu hb)
  unfold canopyFare; dsimp only
  have hv (v : P.Points) : roadmap P (U 0) v i P.L.val=1 := by simp [roadmap,hp,Pressure.one]
  simp only [agora,G.mat_mul,G.mat_inv]
  refine square_sing (square_sing (pre_choir h p hp he.lower) (crossing_stamp he hp i) ?_ ?_) ?_ ?_ ?_
  · intro v; simp [hp,cap_ground h]
  · simp [hv]
  · exact hh
  · intro v; rw [hv]; simp [hp,cap_ground h]
  intro v; simp [hp,cap_ground h,hall_one]

def airfare (G : Gauge) (j m : ℕ) (C : ℝ) := portrait j*canopyFare G j m C
def airplay (G : Gauge) (j m : ℕ) (C : ℝ) := encore (bell G) 1 (airfare G j m C) m
lemma airplay_funds {A : Audience α} (i : Axis) (h : P.Branches K G) (p : Army U 0) (hp : U 0=1) (he : Sung P R U m C) : Gallop A R (fun _ x => G.mat (victoryBox P (U x) i)) m (airplay G P.J m C) := by
  have hv := (agora_fare i h p hp he).budget (painted P.J) (salon_stamp _)
  have hx : Gallop A R (fun _ x => litBox P (U x) i) m (airfare G P.J m C) := all_average hv
  exact hx.comp (fun v => by rw [hp,lit_ground h]) G.focus_diff

lemma dome_thin (h : Army U 0) (hp : U 0=1) : Sung P (fun _ _ => False) U 0 0 := by
  intro i; rw [mul_zero]; exact Gallop.blank (fun i => h _) le_rfl
lemma gulf_cost (h : P.Branches K G) (p : Army U 0) (hp : U 0=1) (i : Axis) : Army (fun x v => agora P (U x) v i) 0 :=
    (agora_fare i h p hp (dome_thin p hp)).listen
lemma gulf_height (h : P.Branches K G) (p : Army U 0) (hp : U 0=1) (i : Axis) : ContDiffAt ℝ ω (fun x => litBox P (U x) i) 0 := ContDiffAt.sum fun v _ => (gulf_cost h p hp i v).const_smul _
lemma lit_predict (h : P.Branches K G) (p : Army U 0) (hp : U 0=1) (i : Axis) :
    ∀ᶠ x in 𝓝 0, ∀ j, P.predict K (fun v => agora P (U x) v i) j=victoryBox P (U x) i := by
  let T := fun x v => agora P (U x) v i
  let B := fun x => litBox P (U x) i
  have hh : P.usesBest K (T 0) := by
    apply lt_of_le_of_lt ((P.bond_min _).choose_spec 1)
    simpa [Patch.bondCost,T,hp,agora_zero h] using K.predictor_cut_pos
  have hu := (gulf_cost h p hp i).cont
  have ht : Tendsto B (𝓝 0) (𝓝 1) := (show B 0=1 by simp [B,hp,lit_ground h]) ▸ (gulf_height h p hp i).continuousAt.tendsto
  filter_upwards [hu.eventually ((P.best_open (C:=K)).mem_nhds hh),ht.eventually G.nearest_is_focus] with x hx hr j
  change P.predict K (T x) j=_; rw [Patch.predict,if_pos (show P.usesBest _ _ from hx)]
  exact hr _ ((Branch.min_iff P.weight P.weight_sum _ _).2 (P.bond_min (T x)).choose_spec)

lemma plaza_agree (h : P.Branches K G) (he : Army U 0) (hp : U 0=1) (hb : Army T 0) (hz : T 0=1) (hs : ∀ᶠ x in 𝓝 0,∀ i∈playhouse P,∀ j, U x (i,j)=T x (i,j)) :
    ∀ᶠ x in 𝓝 0, P.selected (U x)=P.selected (T x) ∧ ∀ i,victoryBox P (U x) i=victoryBox P (T x) i ∧ P.selected (hall P (U x) i)=P.selected (hall P (T x) i) := by
  filter_upwards [hs,min_applies (P:=P) (K:=K) he hp,eventually_all.mpr (fun i => min_applies (P:=P) (K:=K) (hallUp he P i) (by rw [hp,hall_one]))] with x hx hk ht
  have heq := dome_select (U:=U x) (V:=T x) h hk (fun i hi => hx i (alley (⟨i,hi⟩ : P.Points)))
  refine ⟨heq,fun i => ?_⟩
  have hv := dome_select h (V:=hall P (T x) i) (ht i) (fun w hw j => hx (w+P.L.val • step i) (rent_fit P (⟨w,hw⟩ : P.Points) i P.L.val le_rfl) j)
  have hA (v : P.Points) : agora P (U x) v i=agora P (T x) v i := by rw [agora,agora,crossing_local v i hx P.L.val le_rfl]; simp only [choirCap,entryCap,entryHat,heq,hv]
  exact ⟨by simp_rw [victoryBox,litBox,hA],hv⟩

section period
variable (t : S.Choices) (h : S.patch.Branches S.kernel G) (hp : Army V 0) (hb : V 0=1)
include h hp hb
-- multiple mesh occurrences not required to take distinct tags.
lemma cape_hood (i : Site c) : ∀ᶠ x in 𝓝 0, S.frames (V x) t.1 i=S.patch.selected (expandAt (S.ratio.embed i) (V x)) := by
  let T := fun x => expandAt (S.ratio.embed i) (V x)
  have he : T 0=1 := by funext z; simp [T,hb,expandAt]
  exact (tagged_here (P:=S.patch) (K:=S.kernel) (U:=T) (fun i => hp _) he).mono (fun _ he => he _)
lemma centered_wire (i : Site c) (j : Axis) : ∀ᶠ x in 𝓝 0,
    bears S t (V x) i = entryCap S.patch (expandAt (S.ratio.embed i) (V x)) ∧
      (bears S t (V x) i)⁻¹ * S.prediction (V x) t (i,j)*bears S t (V x) (i+step j) = victoryBox S.patch (expandAt (S.ratio.embed i) (V x)) j := by
  let P x := expandAt (S.ratio.embed i) (V x)
  have he : P 0=1 := by funext z; simp [P,hb,expandAt];
  have hP : Army P 0 := fun i => hp _
  filter_upwards [lit_predict h hP he j,cape_hood S t h hp hb i,cape_hood S t h hp hb (i+step j)] with z hz hv hu
  have ha : bears S t (V z) i=entryCap S.patch (P z) := by simp [bears,prospect,hv,P]; rfl
  have hx : bears S t (V z) (i+step j)=entryCap S.patch (hall S.patch (P z) j) := by simp [bears,prospect,hu,house_moves,P]; rfl
  let b := (bears S t (V z) i)⁻¹; let d := bears S t (V z) (i+step j)
  let A := S.connector (V z) t.1 (i,j)
  have hk : (fun v => b*A v*d)=(fun v => agora S.patch (P z) v j) := by
    funext v; unfold agora; simp only [b,d,ha,hx,choirCap]; unfold A; simp only [P,StepData.connector,roadmap,house_moves,hv,hu, _root_.mul_inv_rev,inv_inv,mul_assoc]
  refine ⟨ha,?_⟩
  change b*S.patch.predict _ _ _ *d= _
  rw [← (S.patch.bond_gauge (h:=h) b d A (t.2 (i,j))).2,hk]; exact hz _
end period
end YM.Stationary
end

/-!
# Stencil over fields with multiple supports. `Piano` inside
Plaza and repeated coarse roots as needed per output AXIS bundle. Phase flags
in connectors modify future shear; `root=true` always uses fixed CAP of
initial Bg in the oriented Phi. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {P : Patch} {K : KernelChoices} {C : ℝ} {m : ℕ}

abbrev Piano (G : Gauge) (P : Patch) := (Bool × Plaza P × Loc G 1) ⊕ ((Bool × Option Axis × G.ColorIndex) ⊕ (Bool × Loc G 1))
abbrev BassInput (G : Gauge) (P : Patch) := Corn (Piano G P)
-- c=TRUE internal perturbation, coarse link in Bool TRUE separate vertical field for damageC.
def whipF (v : Bool) (b : Plaza P) (i : Axis) : BassInput G P →L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
  toFun x := WithLp.toLp 2 fun j => x (Sum.inl (v,b,coord i,j))
  map_add' a b := rfl
  map_smul' a b := rfl }
def whipC (v : Bool) (a : Option Axis) : BassInput G P →L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
  toFun x := WithLp.toLp 2 fun j => x (Sum.inr (Sum.inl (v,a,j)))
  map_add' a b := rfl
  map_smul' a b := rfl }
def whipV (v : Bool) (a : Axis) : BassInput G P →L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
  toFun x := WithLp.toLp 2 fun j => x (Sum.inr (Sum.inr (v,coord a,j)))
  map_add' a b := rfl
  map_smul' a b := rfl }

-- uniform, no conjugation on tests, norms on finite patches not big torus.
structure StaffP (G : Gauge) (P : Patch) (C : ℝ) (x : BassInput G P) (k : ℕ) : Prop where
  grade : k≤ 2
  fly (v : Bool) (i : Axis) : Hearing (balcony (Plaza P)) k (fun b => whipF v b i x) (inch P.L*C)
  cap v i : ‖whipC v i x‖ ≤ C
  wages v i : ‖whipV v i x‖≤ C

section masks
-- key readings of local variables using Bool v (perturbed? false Bg; true use both)
variable (v : Bool)
def pianoU (x : BassInput G P) : CoverConfig G := fun e => if h : e.1∈playhouse P then
    (if v then G.lieExp (whipF true ⟨_,h⟩ e.2 x) else 1) * G.lieExp (whipF false ⟨_,h⟩ e.2 x)
      else 1
def pianoC (x : BassInput G P) (i : Option Axis) := (if v then G.lieExp (whipC true i x) else 1) * G.lieExp (whipC false i x)
def pianoV (x : BassInput G P) (i : Axis) := G.lieExp (whipV v i x)
lemma piano_origin : pianoU v (0:BassInput G P)=1 := by funext i; unfold pianoU; split <;> simp
lemma pianoC_origin (i) : pianoC v (0:BassInput G P) i=1 := by simp [pianoC]
lemma pianoV_origin (i) : pianoV v (0:BassInput G P) i=1 := by simp [pianoV]
end masks

/-- Uses rooted correction, accessed at ROOT & Axis, width estimates for `r=false`.
 Re-read h at internal longitude. For r=true and pert v=true this is
 `Φ` corrected by m(a base)^-1 times m(pers). For v=false it still cancels. -/
def parkIt (i : Option Axis) (U : CoverConfig G) (P : Patch) := match i with | none => U | some a => hall P U a
def musicStand (r v : Bool) (x : BassInput G P) (i : Option Axis) : G.El := if r then pianoC v x i * (entryCap P (parkIt i (pianoU false x) P))⁻¹ * entryCap P (parkIt i (pianoU v x) P) else pianoC v x i
def poseBox (r v : Bool) (x : BassInput G P) (i : Axis) := musicStand r v x none * victoryBox P (pianoU v x) i * (musicStand r v x (some i))⁻¹
def shieldBox (r v : Bool) (x : BassInput G P) (i : P.Points) := musicStand r v x none * choirCap P (pianoU v x) i
def rocketBox (r : Bool) (x : BassInput G P) (i : P.Points) := -plogC G ((shieldBox r false x i)⁻¹ * shieldBox r true x i)
def wristBox (r : Bool) (x : BassInput G P) (i : Axis) := plogC G (poseBox r true x i*(poseBox r false x i)⁻¹)

-- N and N_b. classical bits evaluated via card. True in N.
def presentsBox (r : Bool) (k : ℝ) (x : BassInput G P) (i : Axis) := k*G.price (pianoV false x i * (poseBox r true x i)⁻¹)
def inuresBox (r : Bool) (k : ℝ) (x : BassInput G P) (i : Axis) := k*G.price (pianoV false x i * (pianoV true x i * poseBox r false x i)⁻¹)

lemma stand_origin (r v : Bool) (i) : musicStand r v (0:BassInput G P) i=1 := by simp [musicStand,piano_origin,pianoC_origin]
lemma shieldBase (h : P.Branches K G) (r v : Bool) (i) : shieldBox r v (0:BassInput G P) i=1 := by simp [shieldBox,piano_origin,stand_origin,cap_ground h]
lemma pose_base (h : P.Branches K G) (r v : Bool) (i) : poseBox r v (0:BassInput G P) i=1 := by simp [poseBox,piano_origin, stand_origin,victory_box0 h]

lemma pose_started (r : Bool) (x : BassInput G P) (i : Axis) : poseBox r false x i=poseBox false false x i := by cases r <;> simp [poseBox,musicStand]
end YM.Stationary
end

/-!
# Fiscal costs under linear inputs. All leaves.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {α : Type} [Fintype α] {X Y Z : Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] {A : Audience α} {G : Gauge} {P : Patch} {K : KernelChoices} {C D μ : ℝ} {m n : ℕ}

section linear
variable (R : X→ℕ→Prop)
lemma steelG (L : α→X→L[ℝ] Y) (h : ∀ i p, R i p → Hearing A p (fun x=> L x i) C) (he : 0≤C) (n) : Gallop A R (fun i x => L i x) n C := by
  refine ⟨fun i => (L i).contDiff.contDiffAt, he, fun j hk hx => ?_⟩
  by_cases hv : j=1
  · subst j; intro u b hp hx
    simp_rw [iteratedFDeriv_one_apply,(L _).fderiv,Fintype.sum_unique]; exact h _ _ (hp _)
  obtain ⟨v,rfl⟩ : ∃ v,j=v+1 := ⟨j-1,by omega⟩
  intro u b hp hx; refine Hearing.sup he (fun i => ?_)
  rw [iteratedFDeriv_succ_apply_right]
  rw [show fderiv ℝ (L i)=fun _ : X => L i from funext fun _ => (L i).fderiv,iteratedFDeriv_const_of_ne (by omega)]; simpa
lemma apollo_cut {F : Y →Z} (hm : m≥ 1) (hp : 0 ≤ μ) (hh : μ ≤ 1) (hc : 0≤C) (u : Y) : apollo F u (μ*C) m ≤ μ*apollo F u C m := by
  unfold apollo; rw [mul_sum]; apply sum_le_sum; intro c _
  simp only [prod_const,card_univ,Fintype.card_fin,mul_pow,mul_left_comm μ]
  gcongr
  have hu : μ^c.length ≤ μ^1 := pow_le_pow_of_le_one hp hh (c.length_pos hm)
  simpa using hu
lemma scaleG {f : α→X→Y} (h : Gallop A R f m (μ*C)) {u : Y} (he : ∀ i,f i 0=u) (hp : 0 ≤ μ) (hq : μ ≤ 1) (hc : 0≤C) {F : Y →Z} (hf : ContDiffAt ℝ ω F u) : Gallop A R (fun i => F ∘ f i) m (μ*encore F u C m) := by
  have hx k : 0 ≤ apollo F u C k := apollo_pos _ _ hc k
  refine ⟨(h.comp he hf).listen, mul_nonneg hp (sum_nonneg fun i _ => hx _),fun k hk hu => Tested.raises (tested_compartment hf h he hk (fun c _ i => (c.partSize_le i).trans hu)) ((apollo_cut hk hp hq hc u).trans (mul_le_mul_of_nonneg_left (single_le_sum (fun i _ => hx i) (mem_range.mpr (Nat.lt_succ_of_le hu))) hp))⟩
end linear

section music
variable (G) (C) (n)
def pian1 := encore (fun a : G.Color => G.mat (G.lieExp a)) 0 C n
def pian2 := choirSquare G (pian1 G C n) (pian1 G C n) 1 1 n

variable {G C n} (v : Bool) (h : 0≤C)
include h
lemma slot1 (j : Axis) : Gallop (balcony (Plaza P)) (StaffP G P C) (fun i x => G.mat (G.lieExp (whipF v i j x))) n (inch P.L*pian1 G C n) := scaleG _ (steelG _ (fun i => whipF v i j) (fun x a p => p.fly v j) (mul_nonneg (inch_pos _).le h) n) (fun i => map_zero _) (inch_pos _).le (inch_le _) h (G.exp_jet.contDiffAt (x:=0))
lemma branded (j : Axis) : Gallop (balcony (Plaza P)) (StaffP G P C) (fun i x => if v then G.mat (G.lieExp (whipF true i j x)) else 1) n (inch P.L*pian1 G C n) := by
  have he := slot1 (G:=G) (P:=P) (n:=n) true h j; cases v
  · exact Gallop.goes _ he.stamp
  exact he
lemma piano_fare : Sung P (StaffP G P C) (pianoU v) n (pian2 G C n) := by
  intro i; let T := slot1 (G:=G) (P:=P) (n:=n) false h i
  have hf := (branded v h (G:=G) (P:=P) (n:=n) i).sings T
  let d := pian1 G C n
  have he : 0≤d := nonneg_of_mul_nonneg_right T.stamp (inch_pos _)
  let f := fun (a : Plaza P) (x : BassInput G P) =>
    ((if v then G.mat (G.lieExp (whipF true a i x)) else 1),G.mat (G.lieExp (whipF false a i x)))
  have hx : Gallop (balcony _) (StaffP G P C) f n (inch P.L*(d+d)) := by rw [mul_add]; exact hf
  apply (scaleG _ hx (u:=(1,1)) (fun i => by simp [f]) (inch_pos _).le (inch_le _) (add_nonneg he he) (F:=chomp G.Mat) (contDiffAt_fst.mul contDiffAt_snd)).renew
  intro a; refine Eventually.of_forall fun x => ?_; classical
  cases v <;> simp [pianoU,chomp,f,a.property]

lemma slot2 (j : Option Axis) : Gallop A (StaffP G P C) (fun _ x => G.mat (G.lieExp (whipC v j x))) n (pian1 G C n) := (steelG _ (fun _ : α => whipC v j) (fun x a (p : StaffP G P C x a) => Hearing.sup (f:=fun _ => whipC v j x) (A:=A) h (fun _ => p.cap v j)) h n).comp (u₀:=0) (fun i => map_zero _) (G.exp_jet.contDiffAt (x:=0))
lemma slot3 (j : Axis) : Gallop A (StaffP G P C) (fun _ x => G.mat (pianoV v x j)) n (pian1 G C n) := (steelG _ (fun _ : α => whipV v j) (fun x a (p : StaffP G P C x a) => Hearing.sup (f:=fun _ => whipV v j x) (A:=A) h (fun _ => p.wages v j)) h n).comp (u₀:=0) (fun i => map_zero _) (G.exp_jet.contDiffAt (x:=0))
lemma ring3 (j : Option Axis) : Gallop A (StaffP G P C) (fun _ x => G.mat (pianoC v x j)) n (pian2 G C n) := by
  let T := slot2 (G:=G) (P:=P) (A:=A) (n:=n) true h j
  have hp : Gallop A (StaffP G P C) (fun _ x => G.mat (if v then G.lieExp (whipC true j x) else 1)) n (pian1 G C n) := by
    cases v
    · exact Gallop.goes _ T.stamp
    exact T
  simp only [pianoC,G.mat_mul]
  refine square_sing hp (slot2 false h j) (fun _ => by simp) (fun _ => by simp)
omit h
lemma piano_army : Army (pianoU v (G:=G) (P:=P)) 0 := by
  have he := piano_fare (G:=G) (P:=P) (n:=0) v (le_refl 0)
  intro i; by_cases h : i.1∈ playhouse P
  · exact (he i.2).listen (⟨_,h⟩)
  simp_rw [pianoU,dif_neg h]; exact contDiffAt_const
end music
end YM.Stationary
end

/-!
# Cover costs ready for stencil extraction. Estimates for centered
presentations ONLY (rooted Φ will be used at qualitative widths).
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {α β : Type} [Fintype α] [Fintype β] {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {A : Audience α} {G : Gauge} {P : Patch} {K : KernelChoices} {C D μ : ℝ} {m n : ℕ}
section fields
variable (G)
def bless (b c : ℝ) (n : ℕ) := choirSquare G b c 1 1 n
def canopy_fare (j n : ℕ) (c : ℝ) := let a := pian2 G c n; bless G (bless G a (airplay G j n a) n) a n
def shield_fare (j n : ℕ) (c : ℝ) := let a := pian2 G c n; bless G a (subbass G j (portrait (j+2)*a) n) n
def rocket_fare (j n : ℕ) (c : ℝ) := let a := shield_fare G j n c; encore (- G.plog) 1 (bless G a a n) n
def springs (j n : ℕ) (c : ℝ) := let a := canopy_fare G j n c; encore G.plog 1 (bless G a a n) n

def paid_mat (k : ℝ) (u : G.Mat) := k*(‖u-1‖^2/G.colorScale^2/2)
lemma toll_chi (k : ℝ) (u : G.El) : paid_mat G k (G.mat u)=k*G.price u := by
  unfold paid_mat; rw [← div_pow]; change k*(G.chord u^2/2)=_; rw [G.chord_price]; ring
lemma cashable (k : ℝ) (z : G.Mat) : ContDiffAt ℝ ω (paid_mat G k) z := contDiffAt_const.mul ((((contDiff_norm_sq ℝ).contDiffAt.comp z (f:=fun x => x-1) (contDiffAt_id.sub contDiffAt_const)).div_const (G.colorScale^2)).div_const 2)

def cashBook (j n : ℕ) (c k : ℝ) := encore (paid_mat G k) 1 (bless G (pian1 G c n) (canopy_fare G j n c) n) n
def cashDamage (j n : ℕ) (c k : ℝ) := let a := pian1 G c n; encore (paid_mat G k) 1 (bless G a (bless G a (canopy_fare G j n c) n) n) n

end fields
lemma chapel {F H : α → X→ G.El} {R : X→ℕ→Prop} (h : Gallop A R (fun i x => G.mat (F i x)) n C) (q : Gallop A R (fun i x => G.mat (H i x)) n D) (hf : ∀ i,F i 0=1) (ht : ∀ i,H i 0=1) : Gallop A R (fun i x => G.mat (F i x * H i x)) n (bless G C D n) := by
  simp_rw [G.mat_mul]
  exact square_sing h q (fun i => by simp [hf]) (fun i => by simp [ht])
section stores
variable (h : P.Branches K G) (he : 0≤C)
include h he
lemma canopy_sits (v : Bool) (i : Axis) : Gallop A (StaffP G P C) (fun _ x => G.mat (poseBox false v x i)) n (canopy_fare G P.J n C) := by
  simp only [poseBox,musicStand,Bool.false_eq_true, ↓reduceIte]
  have hz := piano_fare (P:=P) (G:=G) (n:=n) v he
  have ht := airplay_funds (A:=A) i h (piano_army v) (piano_origin v) hz
  let F j := ring3 (A:=A) (P:=P) (G:=G) (n:=n) v he j
  apply chapel (H:=fun _ x => (pianoC v x (some i))⁻¹) (X:=BassInput G P) (chapel (F none) ht (fun _ => pianoC_origin ..) (fun _ => by rw [piano_origin]; exact victory_box0 h i)) (Gallop.notes_star G (F (some i)))
  · intro a; simp [piano_origin,pianoC_origin, victory_box0 h]
  intro a; simp [pianoC_origin]
lemma shield_sits (v : Bool) : Gallop (balcony P.Points) (StaffP G P C) (fun i x => G.mat (shieldBox false v x i)) n (shield_fare G P.J n C) := by
  have hz := piano_fare (P:=P) (G:=G) (n:=n) v he
  exact chapel (F:=fun _ x => pianoC v x none) (H:=fun i x => choirCap P (pianoU v x) i) (ring3 v he none) (pre_choir h (piano_army v) (piano_origin v) hz.lower) (fun _ => pianoC_origin ..) (fun _ => by rw [piano_origin,cap_ground h]; rfl)
lemma rocket_sits : Gallop (balcony P.Points) (StaffP G P C) (fun i x => rocketBox false x i) n (rocket_fare G P.J n C) := by
  refine Gallop.comp (T:=-G.plog) (u₀:=1) (chapel (H:=fun i x => shieldBox false true x i) (F:=fun i x => (shieldBox false false x i)⁻¹) (Gallop.notes_star G (shield_sits (n:=n) h he false)) (shield_sits h he true) (fun i => by simp [shieldBase h]) (fun i => shieldBase h ..)) (fun i => by simp [shieldBase h]) G.plog_diff.neg
lemma wrist_sits (i : Axis) : Gallop A (StaffP G P C) (fun _ x => wristBox false x i) n (springs G P.J n C) := Gallop.comp (T:=G.plog) (chapel (F:=fun _ x => poseBox false true x i) (H:=fun _ x => (poseBox false false x i)⁻¹) (canopy_sits (A:=A) (n:=n) h he true i) (Gallop.notes_star G (canopy_sits h he false i)) (fun _ => pose_base h ..) (fun _ => by simp [pose_base h])) (u₀:=1) (fun _ => by simp [pose_base h]) G.plog_diff
lemma books_paid (k : ℝ) (i : Axis) : Gallop A (StaffP G P C) (fun _ x => presentsBox false k x i) n (cashBook G P.J n C k) := by
  simp_rw [presentsBox,← toll_chi]
  apply Gallop.comp (A:=A) (chapel (X:=BassInput G P) (F:=fun _ x => pianoV false x i) (H:=fun _ x => (poseBox false true x i)⁻¹) (slot3 false he i) (Gallop.notes_star G (canopy_sits h he true i)) (fun _ => pianoV_origin ..) (fun _ => by simp [pose_base h])) (T:=paid_mat G k) (u₀:=1) (fun _ => by simp [pose_base h,pianoV_origin]) (cashable G k 1)
lemma books_damage (k : ℝ) (i : Axis) : Gallop A (StaffP G P C) (fun _ x => inuresBox false k x i) n (cashDamage G P.J n C k) := by
  simp_rw [inuresBox,← toll_chi]
  refine Gallop.comp (A:=A) (chapel (F:=fun _ x => pianoV false x i) (H:=fun _ x => (pianoV true x i * poseBox false false x i)⁻¹) (slot3 (G:=G) (P:=P) (A:=A) (n:=n) false he i) ?_ (fun _ => pianoV_origin ..) (fun _ => by simp [pianoV_origin,pose_base h])) (T:=paid_mat G k) (u₀:=1) (fun _ => by simp [pose_base h,pianoV_origin]) (cashable G k 1)
  exact Gallop.notes_star G (chapel (F:=fun _ x => pianoV true x i) (H:=fun _ x => poseBox false false x i) (slot3 (A:=A) (P:=P) (G:=G) (n:=n) true he i) (canopy_sits h he false i) (fun _ => pianoV_origin ..) (fun _ => pose_base h ..))
end stores
end YM.Stationary
end

/-!
# Template reading at actual patch. Log routines use `costume`: rooted
fixed m or centered recomputed. Equality at same germs, no covariance
comparison at positive order. No translation independence assumed.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {c f : Side} {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {G : Gauge} {P : Patch} {K : KernelChoices} (S : StepData c f)

-- reading fields. `Bang` input background perturb. `mix` accepts shared coords.
abbrev Bang (G : Gauge) (c f : Side) := Point G c f × (Vault G c f × Link G c)
-- indexes: c field false = external B, c true oracle support. Either externally periodic or directionally tiled.
def pianist (i : Site c) : Bang G c f →L[ℝ] BassInput G S.patch := LinearMap.toContinuousLinearMap {
  toFun x p := match p with
    | .inl (false,v,j) => x.1.2.1 (wrap f v.val+S.ratio.embed i,j)
    | .inl (true,v,j) => x.2.1.1 (wrap f v.val+S.ratio.embed i,j)
    | .inr (.inl (false,j,k)) => x.1.2.2 ((j.map fun a => i+step a).getD i,vac,k)
    | .inr (.inl (true,j,k)) => x.2.1.2 ((j.map fun a => i+step a).getD i,vac,k)
    | .inr (.inr (false,j)) => x.1.1 (i,j)
    | .inr (.inr (true,j)) => x.2.2 (i,j)
  map_add' a b := funext fun i => by rcases i with ⟨⟨⟩ | ⟨⟩,k⟩ | (⟨⟨⟩|⟨⟩,k⟩|⟨⟨⟩|⟨⟩,k⟩) <;> rfl
  map_smul' t x := funext fun i => by rcases i with ⟨⟨⟩ | ⟨⟩,k⟩ | (⟨⟨⟩|⟨⟩,k⟩|⟨⟨⟩|⟨⟩,k⟩) <;> rfl }

section notes
variable (t : S.Choices)

def initialBang (v : Bool) (x : Bang G c f) : Joint G c f := if v then Stationary.extend x.2.1 * Stationary.extend x.1.2 else Stationary.extend x.1.2
def finalBang (r v : Bool) (x : Bang G c f) := if r then ((initialBang v x).1,(initialBang v x).2 * (bears S t (initialBang false x).1)⁻¹) else dress (fedora S t) (initialBang v x)
lemma bank_fine (r v : Bool) (x : Bang G c f) : (finalBang S t r v x).1=(initialBang v x).1 := by cases r <;> rfl

omit t in
lemma notes_touched (x : Bang G c f) (i : Site c) (v : Bool) : ∀ a ∈ playhouse S.patch,∀ j,
    pianoU v (pianist S i x) (a,j) = expandAt (S.ratio.embed i) (initialBang v x).1 (a,j) := by
  intro a ha j
  unfold pianoU expandAt
  dsimp only; rw [dif_pos ha]; cases v <;> simp only [initialBang,Bool.false_eq_true,↓reduceIte,Stationary.extend,Prod.fst_mul, Pi.mul_apply,input_color,one_mul] <;> rfl
omit t in
lemma piano_tops (x : Bang G c f) (i : Site c) (j : Option Axis) (v : Bool) : pianoC v (pianist S i x) j=(initialBang v x).2 ((j.map fun a => i+step a).getD i) := by
  cases v <;> simp only [initialBang,Stationary.extend,Prod.snd_mul,Pi.mul_apply,pianoC,Bool.false_eq_true,↓reduceIte,one_mul,switch_color] <;> rfl


omit t in
lemma initial_nice (v : Bool) : Thaw (initialBang (G:=G) (c:=c) (f:=f) v) 0 := by
  have he : Thaw (fun x : Bang G c f => Stationary.extend x.1.2) 0 := Thaw.through (contDiffAt_snd.comp (0:Bang G c f) contDiffAt_fst)
  cases v
  · exact he
  exact (Thaw.through (contDiffAt_fst.comp (0:Bang G c f) contDiffAt_snd) : Thaw (fun x : Bang G c f => Stationary.extend x.2.1) 0).mul he
lemma initial_zero (v : Bool) : initialBang v (0 : Bang G c f)=1 := by cases v <;> simp [initialBang]

lemma fixedCap_at (r : Bool) (x : Bang G c f) : finalBang S t r false x=dress (fedora S t) (Stationary.extend x.1.2) := by cases r <;> rfl
def headOn (r : Bool) (x : Bang G c f) := if r then dress (fedora S t) (Stationary.extend x.1.2) else Stationary.extend x.1.2
def buffOn (G : Gauge) (r : Bool) : Robe G c f := if r then 1 else fedora S t
lemma stayBack (r : Bool) (x : Bang G c f) : finalBang S t r false x=dress (buffOn S t G r) (headOn S t r x) := by
  cases r; · rfl
  rw [fixedCap_at]; simp [buffOn,headOn]
lemma pulledOn (r : Bool) (x : Bang G c f) : finalBang S t r true x=atire (buffOn S t G r) (headOn S t r x) x.2.1 := by
  cases r; · rfl
  simp only [finalBang,buffOn,atire,dress_one,headOn,↓reduceIte]; refine Prod.ext rfl ?_; simp [initialBang,fedora,dress,mul_assoc]

section fit
variable (u : S.patch.Branches S.kernel G)
include u
lemma piano_pact (v : Bool) (i : Site c) : ∀ᶠ x : Bang G c f in 𝓝 0,
    let P := expandAt (S.ratio.embed i) (initialBang v x).1
    let T := pianoU v (pianist S i x)
    S.patch.selected P=S.patch.selected T ∧ ∀ a,victoryBox S.patch P a=victoryBox S.patch T a ∧ S.patch.selected (hall S.patch P a)=S.patch.selected (hall S.patch T a) := by
  let Y x := expandAt (S.ratio.embed i) (initialBang v (x:Bang G c f)).1
  have ht : Y 0=1 := by ext1 i; simp [Y,initial_zero,expandAt]
  let A := pianist (G:=G) S i
  have ha : Army (pianoU v∘A) 0 := Army.comp (w:=fun x => A x) (g:=pianoU v) (by change Army (pianoU v) (A 0); rw [map_zero]; exact piano_army v) A.contDiff.contDiffAt
  exact plaza_agree u (U:=Y) (fun i => (initial_nice (G:=G) (c:=c) (f:=f) v).1 _) ht ha (by change pianoU _ (A 0)= _; rw [map_zero]; exact piano_origin v) (Eventually.of_forall fun x a h j => (notes_touched S x i v a h j).symm)
lemma cranked (r v : Bool) (i : Site c) : ∀ᶠ x : Bang G c f in 𝓝 0,∀ o,
      musicStand r v (pianist S i x) o =
      let k := (o.map fun a => i+step a).getD i
      (finalBang S t r v x).2 k * bears S t (initialBang v x).1 k := by
  let T := fun v : Bool => fun x : Bang G c f => (initialBang v x).1
  have ht b : Army (T b) 0 := (initial_nice b).1
  have hT b : T b 0=1 := congr_arg Prod.fst (initial_zero b)
  have he b : ∀ᶠ x in 𝓝 (0:Bang G c f),∀ o : Option Axis,
      bears S t (T b x) ((o.map fun a => i+step a).getD i)= entryCap S.patch (parkIt o (pianoU b (pianist S i x)) S.patch) := by
    filter_upwards [piano_pact S u b i, eventually_all.mpr fun k => centered_wire S t u (ht b) (hT b) k 0] with x hx hp
    intro o; cases o with
    | none => simp only [Option.map,Option.getD,parkIt]; rw [(hp i).1]; simp only [entryCap,entryHat,T,hx.1]
    | some a =>
      simp only [Option.map,Option.getD]; rw [(hp (i+step a)).1, ← house_moves S (T b x) i a]; simp only [parkIt,entryCap,entryHat,T,(hx.2 a).2]
  filter_upwards [he v,he false] with x hx hz
  intro o; dsimp only
  simp only [finalBang, T, piano_tops] at *
  cases r <;> simp [musicStand,dress,fedora,piano_tops, ← hz, ← hx]
lemma fit_ward (r v : Bool) (i : Site c) (a : Axis) : ∀ᶠ x : Bang G c f in 𝓝 0,
    poseBox r v (pianist S i x) a=ribbon S t (finalBang S t r v x) (i,a) := by
  filter_upwards [piano_pact S u v i,cranked S t u r v i,centered_wire S t u (initial_nice (G:=G) (c:=c) (f:=f) v).1 (by rw [initial_zero]; rfl) i a] with x hx hp hz
  unfold poseBox; rw [hp,hp, ← (hx.2 a).1, ← hz.2]
  change _= (finalBang S t r v x).2 i * S.prediction (finalBang S t r v x).1 t (i,a) * ((finalBang S t r v x).2 (i+step a))⁻¹
  rw [bank_fine]; dsimp only [Option.getD,Option.map]; group
lemma fit_shield (r v : Bool) (i : Site f) : ∀ᶠ x : Bang G c f in 𝓝 0,
    shieldBox r v (pianist S (S.ratio.parent i) x) (hatPoint S i)=shield S t (finalBang S t r v x) i := by
  let k := S.ratio.parent i
  filter_upwards [piano_pact S u v k,cranked S t u r v k,centered_wire S t u (initial_nice (G:=G) (c:=c) (f:=f) v).1 (by rw [initial_zero]; rfl) k 0,
        cape_hood S t u (initial_nice (G:=G) (c:=c) (f:=f) v).1 (by rw [initial_zero]; rfl) k] with x hx hp hu he
  unfold shieldBox shield
  change musicStand r v (pianist S k x) none * choirCap _ (pianoU v (pianist S k x)) _=(finalBang S t r v x).2 k * S.frames (finalBang S t r v x).1 t.1 k (hatPoint S i)
  simp only [bank_fine,he,hp,Option.getD,Option.map];
  rw [hu.1]; unfold choirCap entryCap entryHat; simp only [hx.1]; group
end fit
end notes
end YM.Stationary
end

/-!
# Standing charges read and identities for vertical and Φ gradient tasks,
real templates including qualitative (rooted-only) fits. Numerator rate to
be extracted only after linear input/wave choice.
-/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Audience Exterior Precision Bloch Wilson Laurent Matrix Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {P : Patch} {K : KernelChoices} (S : StepData c f)

section lit
variable (h : P.Branches K G) (r v : Bool)
include h
lemma tower_carries (i : Option Axis) : ContDiffAt ℝ ω (fun x : BassInput G P => G.mat (entryCap P (parkIt i (pianoU v x) P))) 0 := by
  cases i with
  | none => exact cap_fold h (piano_army v) (piano_origin v)
  | some i => exact cap_fold h (hallUp (piano_army v) _ _) (by rw [piano_origin,parkIt,hall_one])
lemma actors : Army (musicStand r v : BassInput G P→ Option Axis→G.El) 0 := by
  have hf : Army (pianoC v : BassInput G P → Option Axis → G.El) 0 := fun i => (ring3 (A:=balcony P.Points) (G:=G) (P:=P) (n:=0) v (le_refl 0) i).listen P.center
  cases r
  · exact hf
  let F v := fun (x : BassInput G P) i => entryCap P (parkIt i (pianoU v x) P)
  have hx v : Army (F v) 0 := tower_carries h v
  exact (hf.mul (hx false).inv).mul (hx v)
lemma poseCast : Army (poseBox r v : BassInput G P → Axis → G.El) 0 := by
  let F := musicStand (G:=G) (P:=P) r v
  intro i
  have hq := airplay_funds (A:=balcony P.Points) i h (piano_army v) (piano_origin v) (piano_fare (n:=0) v (le_refl 0)) |>.listen P.center
  exact ((actors h r v none).mul hq).mul ((actors h r v).inv (some i))
lemma shieldCast : Army (shieldBox r v : BassInput G P→ P.Points→ G.El) 0 := fun i =>
    (actors h r v none).mul (cap_thaw h (piano_army v) (piano_origin v) i)
lemma rocketThis (i : P.Points) : ContDiffAt ℝ ω (fun x : BassInput G P => rocketBox r x i) 0 := by
  let F := fun x : BassInput G P => G.mat ((shieldBox r false x i)⁻¹ * (shieldBox r true x i))
  have he : ContDiffAt ℝ ω F 0 := ((shieldCast h r false).inv.mul (shieldCast h r true)) i
  have hv : F 0=1 := by simp [F,shieldBase h]
  exact ((show ContDiffAt ℝ ω G.plog (F 0) by rw [hv]; exact G.plog_diff).comp _ he).neg
lemma wrist_this (i : Axis) : ContDiffAt ℝ ω (fun x : BassInput G P => wristBox r x i) 0 := by
  let F := fun x : BassInput G P => G.mat (poseBox r true x i*(poseBox r false x i)⁻¹)
  have he : ContDiffAt ℝ ω F 0 := ((poseCast h r true).mul (poseCast h r false).inv) i
  have hv : F 0=1 := by simp [F,pose_base h]
  exact (show ContDiffAt ℝ ω G.plog (F 0) by rw [hv]; exact G.plog_diff).comp _ he
lemma presents_this (k : ℝ) (i : Axis) : ContDiffAt ℝ ω (fun x : BassInput G P => presentsBox r k x i) 0 := by
  have hv := slot3 (A:=balcony P.Points) (G:=G) (P:=P) (n:=0) false (le_refl 0) i
  exact contDiffAt_const.mul (matrix_price_jet ((hv.listen P.center).mul ((poseCast h r true).inv i)))
lemma inuresThis (k : ℝ) (i : Axis) : ContDiffAt ℝ ω (fun x : BassInput G P => inuresBox r k x i) 0 := by simp_rw [inuresBox,pose_started]; exact (books_damage (A:=balcony P.Points) (n:=0) h (le_refl 0) k i).listen P.center
end lit

-- match whole applied outputs
variable (t : S.Choices) (h : S.patch.Branches S.kernel G)
include h
lemma ethic (i : Site f) (j : G.ColorIndex) (r : Bool) : ∀ᶠ x : Bang G c f in 𝓝 0,
    rocket S t (buffOn S t G r) (headOn S t r x) x.2.1 (i,vac,j)=
      rocketBox r (pianist S (S.ratio.parent i) x) (hatPoint S i) j := by
  filter_upwards [fit_shield S t h r false i,fit_shield S t h r true i] with x hx hh
  change gaugeColor (rocket S t (buffOn S t G r) (headOn S t r x) x.2.1) i j=_
  rw [rocketBox,hx,hh,pulledOn,stayBack,rocket,map_neg]
  simp [frameLog]

lemma edict_pay (i : Site c) (k : Axis) (j : G.ColorIndex) (r : Bool) : ∀ᶠ x : Bang G c f in 𝓝 0,
    worn S t (buffOn S t G r) (headOn S t r x) x.2.1 (i,coord k,j)=wristBox r (pianist S i x) k j := by
  filter_upwards [fit_ward S t h r false i k,fit_ward S t h r true i k] with x hx hh
  rw [wristBox,hx,hh,stayBack S t,pulledOn S t]
  let M := headOn S t r x; let C := buffOn S t G r
  let U := ribbon S t (atire C M x.2.1)*(ribbon S t (dress C M))⁻¹
  exact congr_arg (fun z : G.Color => z j) (content_at U i k)

omit h in
lemma direct_whip (x : Bang G c f) (v : Bool) (i : Site c) (j) :
    pianoV v (pianist S i x) j=(input G c (if v then x.2.2 else x.1.1)) (i,j) := by
  rw [input_color]; cases v <;> rfl
lemma boom_line (r : Bool) : ∀ᶠ x : Bang G c f in 𝓝 0,
    tickets S (input G c x.1.1) (ribbon S t (atire (buffOn S t G r) (headOn S t r x) x.2.1))=∑ i : Site c,∑ j : Axis,presentsBox r S.kernel.penalty (pianist S i x) j := by
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (fit_ward S t h r true i))] with x hx
  unfold tickets; rw [Fintype.sum_prod_type,Finset.mul_sum]; simp_rw [Finset.mul_sum,presentsBox,direct_whip, hx,pulledOn S t]; rfl
lemma inured_line (r : Bool) : ∀ᶠ x : Bang G c f in 𝓝 0,
    inure S (input G c x.1.1) (ribbon S t (dress (buffOn S t G r) (headOn S t r x))) x.2.2=∑ i : Site c,∑ j : Axis,inuresBox r S.kernel.penalty (pianist S i x) j := by
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (fit_ward S t h r false i))] with x hx
  unfold inure tickets; rw [Fintype.sum_prod_type,Finset.mul_sum]; simp_rw [Finset.mul_sum,inuresBox,direct_whip,hx,stayBack S t]; rfl
end YM.Stationary
end
