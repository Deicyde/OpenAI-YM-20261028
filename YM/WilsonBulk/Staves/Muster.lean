import YM.WilsonBulk.Staves.Flags

/-!
# Local two-ended link force from FULL coherent formal gauge pillar.

Generator uses two-place endpoint meter keeping coincident endpoints on
small period. Only assigns costs for literal finite Taylor coefficients.
No complex strip (in gauge params) for preserving moments.
Leading generator is outward-forward difference `d b` by placing exp(-b) left.
Primitive `jack` near local unit chord logarithm specialized (plog actual). -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Lattice Laurent Function Filter Bloch Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {α β : Type} {G : Gauge} {i j : G.ColorIndex}
variable {c n : Side}
-- call three terminal ports
abbrev Flap := Bool -- TRUE positive gauge from downstream link end
abbrev Boot (G : Gauge) := Chamber G.ColorIndex (Flap × G.ColorIndex)
abbrev Frosh (G : Gauge) := Tabletop (Boot G)
abbrev Wisp (G : Gauge) := Tabletop G.ColorIndex
abbrev lid (G : Gauge) := priceScreen (G:=G) (α:=G.ColorIndex) id
abbrev sprig (i : G.ColorIndex) := Sum.inl (β:=Flap × G.ColorIndex) i
abbrev heel (f : Flap) (i : G.ColorIndex) := Sum.inr (α:=G.ColorIndex) (f,i)
-- using sign left -, right + (curtainK uses inverse at right). 
attribute [local instance] Gauge.frobInner

def braid (t : Bool) (z : Frosh G) := priceScreen (heel (G:=G) t) z
def meadow (z : Frosh G) := G.lieExp (-braid false z) * G.lieExp (priceScreen (sprig (G:=G)) z) * G.lieExp (braid true z)
def jack (m : G.ColorIndex) (z : Frosh G) := G.plog (G.mat (meadow z)) m
lemma jack_zero (m : G.ColorIndex) : jack m 0=0 := by simp [jack,meadow,braid]
lemma bootForce : ContDiffAt ℝ ω (fun z:Frosh G=>G.mat (meadow z)) 0 := by
  let H (i:G.ColorIndex→ Boot G):=priceScreen (G:=G) i; let K (t:Flap) := H (heel t)
  have hp (F : Frosh G→L[ℝ] G.Color) : ContDiffAt ℝ ω (fun z:Frosh G=> G.mat (G.lieExp (F z))) 0 := G.exp_jet.contDiffAt.comp (f:=F) _ F.contDiff.contDiffAt
  exact ((hp (- K false)).mul (hp (H sprig))).mul (hp (K true))
lemma jack_height (m : G.ColorIndex) : ContDiffAt ℝ ω (jack m) 0 := by
  let e:= WithLp.linearEquiv 2 ℝ (Wisp G);
  have hz:= (show ContDiffAt ℝ ω G.plog (G.mat (meadow (0:Frosh G))) from by simp only [meadow,braid,map_zero,neg_zero,G.mat_lieExp_zero,G.mat_one,mul_one]; exact G.plog_diff).comp (f:= (fun x=>G.mat (meadow x))) (0:Frosh G) bootForce
  exact contDiffAt_pi.mp (e.toContinuousLinearEquiv.contDiff.contDiffAt.comp (x:=0) hz) m

def walkway (v : Wisp G) : Frosh G := Sum.elim v 0
lemma walkway_zero : walkway (0:Wisp G)=0:= funext fun i=> by cases i <;> rfl
lemma walkway_height : ContDiff ℝ ω (walkway (G:=G)) := by apply contDiff_pi.mpr; rintro (i|i); exacts [contDiff_apply ℝ ℝ i,contDiff_const]
lemma flash_0 {α : Type} [Fintype α] : flash (fun _:Tabletop α=>0) = 0 := by unfold flash; rw [ink_const,map_zero,map_zero]; ext1 i; rw [zoom_power, map_zero,map_zero]
lemma walkway_expose : exposure (walkway (G:=G))=Sum.elim named 0 := by ext1 i; cases i with
  | inl i=> exact flash_named _
  | inr i=> exact flash_0
-- sign output FIXS. Tag maybe legitimate silence. price relief.

def lever (t : Bool) (i j : G.ColorIndex) : Wisp G → ℝ:= leafD (heel t j) (jack i) ∘ walkway
def motive (t : Bool) (i j : G.ColorIndex) : Tape G.ColorIndex := ink (lever t i j)
lemma lever_birth (t : Bool) (m i : G.ColorIndex) : lever t m i 0=(if m=i then if t then 1 else -1 else 0) := by
  -- proof using line lift composition for one-variable via socket or fderiv
  let V : G.Color := lid G (spike i)
  let D (v:ℝ) := v • (spike (heel t i):Frosh G)
  let F:= if t then V else -V
  have hz (f : Bool) (v : ℝ) : braid f (D v) = if f=t then v • V else 0 := by
    unfold braid D; rw [map_smul]; ext k
    change v*spike (heel t i) (heel f k)= (if f=t then v • V else 0) k; split
    next h=>rw [h]; simp [heel,V,lid,priceScreen] -- inspect
    next h=> simp [heel,h,spike]
  have hD (v : ℝ) : priceScreen (sprig (G:=G)) (D v)=0 := by unfold D; rw [map_smul]; ext j; change v*spike _ _=0; simp
  have hp : (fun v=> jack m (D v))=ᶠ[𝓝 0] fun v : ℝ=> v*F m := by
    have ht:= tendsto_id.smul (tendsto_const_nhds (x:=F)) (l:=𝓝 (0:ℝ)) (f:=fun t : ℝ=> t); -- fix
    rw [zero_smul] at ht
    filter_upwards [ht.eventually G.plog_left] with z h
    rw [jack, meadow, hz,hz,hD, G.mat_lieExp_zero,mul_one]
    change G.plog (G.mat (G.lieExp _ *G.lieExp _)) m=_; rw [show _*G.lieExp _=G.lieExp (z • F) from ?_, h]; rfl
    unfold F; cases t <;> simp
  have he : HasDerivAt D (spike (heel t i)) 0 := by simpa [D] using (hasDerivAt_id' (0:ℝ)).smul_const (spike (heel t i):Frosh G)
  have hh : HasDerivAt (fun v=>jack m (D v)) (fderiv ℝ (jack m) 0 (spike (heel t i))) 0:= (jack_height _|>.differentiableAt (by simp)|>.hasFDerivAt).comp_hasDerivAt_of_eq 0 he (zero_smul ..).symm
  have hF : HasDerivAt (fun v=> jack m (D v)) (F m) 0 := by apply HasDerivAt.congr_of_eventuallyEq _ hp; simpa using (hasDerivAt_id' (0:ℝ)).mul_const (F m)
  unfold lever leafD Analysis.D; rw [Function.comp_apply,walkway_zero, hh.unique hF]; dsimp only [F]; cases t <;> simp [V,lid,priceScreen ]; split_ifs <;> norm_num -- negative ite normalize
lemma motive_player (t : Bool) (i j : G.ColorIndex) : motive t i j = submit (Sum.elim named (0:(Bool × G.ColorIndex) → Tape G.ColorIndex)) (player (heel t j) (flash (jack i))) := by rw [motive,lever,ink_comp (leaf_at (E:=ℝ) (heel t j) (jack_height i)) (walkway_height.contDiffAt) walkway_zero, walkway_expose,flash_player (jack_height i) (jack_zero i)]
lemma motive_zero (t : Flap) (i j : G.ColorIndex) : PowerSeries.coeff 0 (motive t i j)=MvPolynomial.C (if i=j then if t then 1 else -1 else 0) := by rw [PowerSeries.coeff_zero_eq_constantCoeff,motive,ink_norm,lever_birth]
end Parapet
end YM.WilsonBulk
