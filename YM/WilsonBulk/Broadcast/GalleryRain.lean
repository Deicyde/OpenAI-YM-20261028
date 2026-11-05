import YM.WilsonBulk.Broadcast.Compote
import YM.WilsonBulk.Build.Regalia
import YM.Next.STATIONARY.FrameEst.Stencils

/-!
# Translation-planting actual frame/penalty (same G,K,O)

Use accepted Stage argument centered_patch prediction. Recover physical log
not relative to center gauge via right multiplication/add inversion exactly.
Score stem Dept uses only `playhouse`; equals any literal tags in germ by
Stationary centered_wire. Tape grammar charges nonpredating width at any σ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior
open Work.F08 RG Sheet Pert.Bulk Atelier
variable {α β γ : Type} {c f L : Side} {G : Gauge} {P : Patch} {S : StepData c f} {K : KernelChoices}
-- no body α constraints beyond Type

abbrev Cloth (G : Gauge) := Loc G 1
abbrev BoltL (G : Gauge) (P : Patch) := Plaza P × Cloth G ⊕ Cloth G -- local conditions
abbrev Screen (G : Gauge) (P : Patch) := Tabletop (BoltL G P)
abbrev Wharf (G : Gauge) (P : Patch) := Echelon (Cloth G) (Cloth G) P.L
def priceScreen (k : G.ColorIndex→α) [Fintype α] : Tabletop α→L[ℝ] G.Color := LinearMap.toContinuousLinearMap {
  toFun x:= WithLp.toLp 2 (x∘ k)
  map_add' _ _:= rfl
  map_smul' _ _:=rfl }
attribute [local instance] Gauge.frobInner

def rainU (P : Patch) (G : Gauge) (x : Screen G P) : Wilson.CoverConfig G := fun e => if h:e.1∈playhouse P then G.lieExp (priceScreen (fun k=>Sum.inl (⟨e.1,h⟩,coord e.2,k)) x) else 1

def rainV (P : Patch) (G : Gauge) (x : Screen G P) (i : Axis) := G.lieExp (priceScreen (fun j=>Sum.inr (coord i,j)) x)
lemma rain_Ω : Army (rainU P G) 0 := by
  intro i; by_cases h:i.1∈playhouse P; swap
  · simp [rainU,h,contDiffAt_const]
  let U:=priceScreen (α:=BoltL G P) (fun k:G.ColorIndex=>Sum.inl (⟨i.1,h⟩,coord i.2,k)); simp only [rainU,dif_pos h]; exact G.exp_jet.contDiffAt.comp (f:=U) _ U.contDiff.contDiffAt
lemma rain_birth : rainU P G 0=1 := by ext1 i; by_cases h:i.1∈playhouse P <;> simp [rainU,h]
lemma rain_v : Army (rainV P G) 0:= fun i=> G.exp_jet.contDiffAt.comp (f:=priceScreen (α:=BoltL G P) (fun j:G.ColorIndex=>Sum.inr (coord i,j))) _ (priceScreen (α:=BoltL G P) (fun j:G.ColorIndex=>Sum.inr (coord i,j))).contDiff.contDiffAt

-- actual portal

def looming (i : Axis) (x : Screen G P) : G.El := entryCap P (rainU P G x)*victoryBox P (rainU P G x) i * (entryCap P (hall P (rainU P G x) i))⁻¹

def splatter (P : Patch) (G : Gauge) (s : ℝ) (x : Screen G P) := s* ∑ i:Axis,G.price (rainV P G x i * (looming i x)⁻¹)
lemma loom_song (h : P.Branches K G) : Army (fun x:Screen G P=>fun i=>looming i x) 0 := by
  let U:= rainU P G; let F x:= entryCap P (U x); let E x i:=entryCap P (hall P (U x) i)
  have hU : ContDiffAt ℝ ω (fun x=> G.mat (F x)) 0:= cap_fold h rain_Ω rain_birth
  have hE : Army E 0 := fun i=> cap_fold h (hallUp (U:=U) rain_Ω _ _) (by rw [show U 0=1 from rain_birth,hall_one])
  intro i
  have hv : ContDiffAt ℝ ω (fun x=> G.mat (victoryBox P (U x) i)) 0:= by
    unfold victoryBox; apply ContDiffAt.comp (g:=(fun i=>G.mat (G.focus i))) (f:=fun x=>litBox P (U x) i); rw [show U 0=1 from rain_birth, lit_ground h]; exact G.focus_diff
    exact gulf_height h rain_Ω rain_birth i
  exact (hU.mul hv).mul (hE.inv i)
lemma splattered (h : P.Branches K G) (s : ℝ) : ContDiffAt ℝ ω (splatter P G s) 0:= ContDiffAt.mul contDiffAt_const (ContDiffAt.sum (fun i _=> matrix_price_jet ((rain_v.mul (loom_song h).inv) i)))

-- reading through promenade & plaza. Includes true all-tag q-expression.

def stake (P : Patch) (G : Gauge) (e : BoltL G P) : Market (Wharf G P) := e.elim (fun p=>(ascent (Cloth G) P.L (p.1.val,p.2))) (fun p=>descent (Cloth G) _ (0,p))
def rung (S : StepData c f) (G : Gauge) := socket ((promenade (Cloth G) (Cloth G) S.ratio).symm) -- not depends z, maybe remove
def tackle (S : StepData c f) (G : Gauge) (z : Site c) := (socket (ladder (stake S.patch G) z)).comp (rung S G)
lemma rung_fare (z : Site c) (b : Plaza S.patch) (i : Axis) (j : G.ColorIndex) (x : ReadingV G c f) :
    tackle S G z x (Sum.inl (b,coord i,j)) = x (Sum.inl (wrap f b.val+ S.ratio.embed z,(coord i,j))) := by
  let p:= (b.val,(coord i,j)); let T:= promenade (Cloth G) (Cloth G) S.ratio
  change x (T.symm (rolls z _ (small c _ (ascent _ _ p))))=x (Sum.inl (rolls (S.ratio.embed z) _ (small f _ p)))
  rw [← ascent_bucks S.ratio p,ascent_roll,Equiv.symm_apply_apply] -- T
lemma rung_toll (z : Site c) (i : Axis) (j : G.ColorIndex) (x : ReadingV G c f) : tackle S G z x (Sum.inr (coord i,j))=x (Sum.inr (z,(coord i,j))) := by
  let T:=promenade (Cloth G) (Cloth G) S.ratio; let p : Market (Cloth G) := (0,(coord i,j)); change x (T.symm (rolls z _ (small c _ (descent _ _ p))))=x _
  rw [← descent_cash S.ratio p, descent_roll, Equiv.symm_apply_apply]; simp [rolls_apply,p,small] -- T
lemma rung_match (z : Site c) (i : Cover) (j : Axis) (x : ReadingV G c f) (h : i∈playhouse S.patch) :
    rainU S.patch G (tackle S G z x) (i,j)=expandAt (S.ratio.embed z) (signal G f (upper _ _ x)) (i,j) := by
  unfold expandAt; rw [rainU, dif_pos h,signal_at]; congr 1; ext k; rw [traces_at]; exact rung_fare ..
lemma rung_rain (z : Site c) (i : Axis) (x : ReadingV G c f) : rainV S.patch G (tackle S G z x) i = signal G c (lower _ _ x) (z,i) := by
  rw [rainV,signal_at]; congr 1; ext k; rw [traces_at]; exact rung_toll ..
end YM.WilsonBulk.Parapet
