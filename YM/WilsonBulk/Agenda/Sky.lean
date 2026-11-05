import YM.WilsonBulk.Solve.Rising

/-!
# Is Land real BEFORE block requests? Part A

Pins Width for each finite demand E and all stage choices. μ_j time-cross chosen *before* L
using unpainted stationary gauge and kinetic Floor aperture. Pre-length estimates then available
for both stencil Taylor moves & Gauge Price Tariffs. §Kbulk demands finite width of h forests
for all orders through E on ALL subsequent steps: this proof does not price at N or compute
width via minima over infinite fine tail. Includes continuity of Λ inputs scale lengths. No
condition on later α actual tuning! Post-companion issued separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
namespace Agenda
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08
open scoped Topology Classical ENNReal BigOperators
variable {A : Type*} {G : Gauge} {K : KernelChoices} {F : MapPrices} {P : Patch} {i j k n E : ℕ} {x a p σ θ μ : ℝ}
/-- Stages j and j+1 possible successor. -/
abbrev after (i j : ℕ) := i ≤ j ∧ j≤ i+1
abbrev αflat (F : MapPrices) (j : ℕ) := min (F.α j) (F.α (j+1))
lemma positive (F : MapPrices) (j : ℕ) : 0 < αflat F j:= lt_min (F.alpha_pos j) (F.alpha_pos (j+1))

structure Lit (G : Gauge) (K : KernelChoices) (F : MapPrices) where
  gamma (j : ℕ) : ℝ
  width (e i : ℕ) : ℝ
  alive (j : ℕ) : 0 < gamma j
  awake (j : ℕ) : gamma j ≤ αflat F j
  Forecast (T : Patch) : T.Branches K G → ∀ R : Model T K, ∃ C:ℝ,0≤C ∧ (flare G T).strip (gamma T.J) C ∧
             ∀ (U : Levels G) (H : Horizon U), H.Suffices F → ∀ (m N), m≤N → stage U m=T.J → Serves G R (H.H N m) (gamma T.J) C
  lighter (e j : ℕ) : 0 < width e j ∧ width e j ≤ min 1 (αflat F j)
  compare {i j : ℕ} : Agenda.after i j → ∀ E, ((E+2:ℕ):ℝ)* width E i ≤ gamma j ∧ ∀ e≤E,width E i ≤ saveWidth e (gamma j)
-- design handy restrictions choose any positive smaller widths satisfying *after both*.
def paint (σ μ : ℝ) (E : ℕ) := ((E+2:ℕ):ℝ)*σ ≤ μ ∧ ∀ e≤E,σ ≤ saveWidth e μ
lemma paint_mono (he : x ≤ σ) (hp : paint σ μ E) : paint x μ E := ⟨(mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ ((E+2:ℕ):ℝ))).trans hp.1,fun i hi=> he.trans (hp.2 i hi)⟩
lemma pigmentation (e : ℕ) (he : 0<μ) : ∃ σ > 0, paint σ μ e := by
  let x := μ/ ((e+2:ℕ):ℝ); have hx : 0<x:= by unfold x; positivity
  let C:= (range (e+1)).inf' ⟨e,mem_range.mpr (by omega)⟩ (fun k=>saveWidth k μ)
  have hp : 0<C:= by refine (lt_inf'_iff ..).mpr ?_; exact fun k _=> save_pos he k
  refine ⟨min x C,lt_min hx hp,?_,fun i hi=>(min_le_right x C).trans (inf'_le _ (mem_range.mpr (by omega)))⟩
  rw [mul_comm]; exact (le_div_iff₀ (by positivity : 0 < ((e+2:ℕ):ℝ))).mp (min_le_left ..)
lemma Lit.exists (G : Gauge) (K : KernelChoices) (F : MapPrices) : Nonempty (Lit G K F) := by
  obtain ⟨g,hp,hK⟩:= preflight G K F; let μ j:=min (g j) (αflat F j); have he j : 0<μ j := lt_min (hp j).1 (positive F _)
  choose σ hv hh using fun (e j : ℕ)=> pigmentation e (he j); let ω e j:= min (min 1 (αflat F j)) (min (σ e j) (σ e (j+1)))
  refine ⟨⟨μ,ω,he,(fun i=>min_le_right ..),fun T ht R=>?_,fun e i=>⟨lt_min (lt_min one_pos (positive F _)) (lt_min (hv ..) (hv ..)), min_le_left ..⟩,fun {i j} h E=>?_⟩⟩
  · obtain ⟨C,hc,hT,H⟩:= hK _ T rfl ht R; exact ⟨C,hc,strip_mono hT (min_le_left ..) le_rfl, fun U H' h m n hm hj=>Serves.lower (H U H' h m n hm hj) (min_le_left ..) le_rfl⟩
  have ht : j=i ∨ j=i+1 := by unfold Agenda.after at h; omega
  rcases ht with rfl|rfl
  · exact paint_mono ((min_le_right ..).trans (min_le_left ..)) (hh E _)
  exact paint_mono ((min_le_right ..).trans (min_le_right ..)) (hh E _)

abbrev SeenRank (F : MapPrices) (G : Gauge) (i : ℕ) := oxidize G (kcap F i)
-- `large` numeric before width. no θ stage. transition slots native
structure Threshold (V : Lit G K F) (a : ℝ) (i j : ℕ) (L : Side) (E : ℕ) : Prop where
  hess_large : kineticBill (F.Ω j) (F.Ω j) (αflat F j) (αflat F i) / L.val ≤ (L.val:ℝ)^(-a)
  keep : αflat F i / L.val ≤ αflat F j / 2
  season : Season L (V.width E j) (V.width E i) (V.gamma j) E
  climb m : 1 ≤ m → m≤ E+1 →
      reflector (V.width E i) (SeenRank F G i) * receipt (Cloth G) (Cloth G) (V.width E i) (V.width E j) (F.Ω j) (fitting m) m / (L.val:ℝ) ≤ (L.val:ℝ)^(-a)
lemma length_fore {a C : ℝ} (ha : a < 1) : ∀ᶠ n : ℕ in atTop,C/(n:ℝ) ≤ (n:ℝ)^(-a) := by
  have h : Tendsto (fun i:ℕ=> (i:ℝ) ^ (-a+1)) atTop atTop:= (tendsto_rpow_atTop (show 0 < -a+1 by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually_ge_atTop C,eventually_gt_atTop 0] with i hi hk; rw [div_le_iff₀ (show 0<(i:ℝ) by positivity)]; rw [Real.rpow_add (show 0<(i:ℝ) by positivity), Real.rpow_one] at hi; exact hi
-- own steel thresholds reified at smoothing stage not launch choices.
lemma Lit.gate (V : Lit G K F) (E : ℕ) (ha : a<1) (he : Agenda.after i j) : ∃ m:ℕ,∀ L:Side,m≤L.val → Threshold V a i j L E := by
  let θ:= V.width E j; let σ:= V.width E i; have hs : 0<θ:= (V.lighter _ _).1
  let f m:= reflector σ (SeenRank F G i) * receipt (Cloth G) (Cloth G) σ θ (F.Ω j) (fitting m) m
  have hh {x : ℝ} (u : ℝ) (h₁ : 0<x) : ∀ᶠ i:ℕ in atTop,u/(i:ℝ) ≤ x:= ((tendsto_const_nhds (x:=u)).div_atTop (tendsto_natCast_atTop_atTop : Tendsto (fun i:ℕ=>(i:ℝ)) atTop atTop)).eventually_le_const h₁ -- x un-generalized
  have hp : ∀ᶠ n:ℕ in atTop, ∀ m:Fin (E+2),f m/(n:ℝ)≤(n:ℝ)^(-a):= eventually_all.mpr (fun m=>length_fore ha)
  have hk : ∀ᶠ n:ℕ in atTop, ∀ p:Side,p.val=n → Threshold V a i j p E := by
    filter_upwards [hp,hessian_invoice (F.Ω j) (F.Ω j) (αflat F i) (αflat F j) a (positive F _) ha, hh (V.gamma j) hs, hh σ (half_pos hs), hh (pulseGrow σ (E+1)) hs] with n hp hv ht hh₁ hh
    rintro U rfl; obtain ⟨h₁,h₂⟩:= V.compare he E
    refine ⟨hv.2,hv.1,⟨hs,(V.lighter _ _).1,V.alive j,(V.lighter _ _).2.trans (min_le_left ..),(V.lighter _ _).2.trans (min_le_left ..),h₁,h₂,ht,hh₁,?_⟩,fun m hm hi=>hp ⟨m,by omega⟩⟩
    convert hh using 1; unfold pulseGrow; ring
  obtain ⟨u,hu⟩:=eventually_atTop.mp hk; exact ⟨u,fun L h=>hu _ h L rfl⟩

lemma Lit.allGates (V : Lit G K F) (a : ℝ) (ha : a<1):∃ τ:ℕ→ℕ, ∀ i j (p:Patch),p.J=j → Agenda.after i j → τ j ≤ p.L.val → ∀ E≤j,Threshold V a i j p.L E := by
  choose M hM using fun E i j=> show ∃ m:ℕ, ∀ L:Side,m≤L.val → Agenda.after i j → Threshold V a i j L E from by
     by_cases h:Agenda.after i j
     · obtain ⟨m,hm⟩:= V.gate E ha h; exact ⟨m,fun L he _=>hm _ he⟩
     exact ⟨0,fun L _ he=> (h he).elim⟩
  let τ j:= (range (j+1)).sup fun E=> (range (j+1)).sup fun i=> M E i j
  exact ⟨τ,fun i j p _ hj he E hk=> hM _ _ _ _ (le_trans (le_trans (le_sup (f:=fun i=> M E i j) (mem_range.mpr (Nat.lt_succ_of_le (show i ≤ j from hj.1)))) (le_sup (f:= fun E=> (range (j+1)).sup fun i=> M E i j) (mem_range.mpr (by omega : E < j+1)))) he) hj⟩
end Agenda
end Parapet
end YM.WilsonBulk
