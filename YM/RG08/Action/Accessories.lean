import YM.RG08.Action.History
/-!
# Ward intermediate carry prices. Pullback along pointwise group-log in
ordinary tori, all periods. Need analytic jets (not Diagram representation). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Staffer
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect Conductor Bloch UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {m c f : Side} (S : StepData c f) (T : Forest S.ratio)
variable {p : ℕ}
-- localized `moveField` symbol; followed by a cross, price then same Ward
abbrev Lacing (G : Gauge)(p : ℕ):= Fin p × Fin 3 × G.ColorIndex
private def cocoa (G : Gauge) (j : Fin p) (s : Fin 3) : Corn (Lacing G p) →L[ℝ] G.Color :=
    LinearMap.toContinuousLinearMap {toFun u := WithLp.toLp 2 (fun k=> u (j,s,k)),map_add' _ _:=rfl,map_smul' _ _:=rfl}
private def music (x : Corn (Lacing G p)) (j : Fin p) : G.Color := G.plog (G.mat (G.lieExp (cocoa G j 0 x) * G.lieExp (cocoa G j 1 x) * (G.lieExp (cocoa G j 2 x))⁻¹))
def minted (q : Fin p→ Loc G 1) (x : Corn (Lacing G p)) := ∏ j,music x j (q j).2
lemma minted_art (q : Fin p→Loc G 1) : AnalyticAt ℝ (minted q) 0 := by
  have hv k : Army (fun x (j : Fin p)=> G.lieExp (cocoa G j k x)) 0 := fun i=> (G.exp_jet.comp (f:=cocoa G i k) (cocoa G i k).contDiff).contDiffAt
  let M (x:Corn (Lacing G p))(j : Fin p):= G.lieExp (cocoa G j 0 x)* G.lieExp (cocoa G j 1 x)*(G.lieExp (cocoa G j 2 x))⁻¹
  have hm : Army M 0 := ((hv 0).mul (hv 1)).mul (hv 2).inv
  have hz j : ContDiffAt ℝ ω (fun x=> G.plog (G.mat (M x j))) 0  :=
    ContDiffAt.comp (f:=fun x=> G.mat (M x j)) _ (show ContDiffAt ℝ ω G.plog (G.mat (M 0 j)) by simp only [M,Gauge.mat_mul,Gauge.mat_inv,map_zero,Gauge.mat_lieExp_zero,Gauge.mat_one,mul_one,star_one]; exact G.plog_diff) (hm j)
  exact (contDiffAt_prod (𝕜:=ℝ) (f:=fun i x=> music x i (q i).2) (t:=univ) (fun i _=> ((PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex=>ℝ) (q i).2).contDiff.contDiffAt.comp _ (hz i)))).analyticAt

def confection (u : Beads (Loc G 1) p)(b:Lacing G p) : Cover×Candles G :=
    if b.2.1=1 then ((u b.1).1,.inr ((u b.1).2.1,b.2.2)) else
      if b.2.1=0 then ((u b.1).1,.inl (vac,b.2.2)) else ((u b.1).1+step (axisEquiv.symm (u b.1).2.1),.inl (vac,b.2.2))
def studs (u : Beads (Loc G 1) p) (z : Site m) : PAC (Candles G) m→L[ℝ] Corn (Lacing G p) :=
    ContinuousLinearMap.pi (fun i=> ContinuousLinearMap.proj (z+wrap m (confection u i).1,(confection u i).2))
private lemma reader (u : Beads (Loc G 1) p) (z : Site m)(x : PAC (Candles G) m) (j : Fin p) :
    let v := (u j).2; let a:=z+wrap m (u j).1
    dragged G m x (a,v)= (music (studs u z x) j) v.2 := by
  intro v a
  let i := axisEquiv.symm v.1
  have hi : coord i=v.1 := axisEquiv.apply_symm_apply v.1
  have ht: (a,v)= (a,coord i,v.2) := by rw [hi]
  let P:=bundleSites (m:=m) (G:=G) x
  have hc : arm G m 0 P.1 (a,vac)= cocoa G j 0 (studs u z x) := by
    ext1 k; unfold cocoa; simp [arm_apply,studs,confection]; rfl
  have he : arm G m 1 P.2 (a,coord i)= cocoa G j 1 (studs u z x) := by
    ext1 k; unfold cocoa; rw [hi]; simp [arm_apply,studs,confection]; rfl
  have hs : arm G m 0 P.1 (a+step i,vac)= cocoa G j 2 (studs u z x) := by
    ext1 k; unfold cocoa; simp [arm_apply,P,a,i,v,studs,confection,add_assoc]; rfl
  rw [ht,← arm_apply G m 1 (dragged G m x) a (coord i) v.2]; change arm G m 1 (moveField P) (a,coord i) v.2=_; rw [moveField, content_at]; unfold shiftLinks Lattice.gauge; rw [encode_link]; simp_rw [switchSite,hc,he,hs]; rfl
lemma studs_read (u : Beads (Loc G 1) p)(z : Site m)(x : PAC (Candles G) m) : minted (Prod.snd ∘ u) (studs u z x)=rosary (fun _=> dragged G m x) z u :=
  prod_congr rfl (fun i _=> Eq.symm (reader u z x i))
lemma studs_len (u : Beads (Loc G 1) p)(b : Lacing G p) : size (confection u b).1 ≤ girth u+1 := by
  unfold confection; have he : size (u b.1).1≤girth u := single_le_sum (f:=fun i=>size (u i).1) (fun _ _=>Nat.zero_le _) (mem_univ _)
  split; exact le_trans he (Nat.le_succ _)
  split; exact le_trans he (Nat.le_succ _)
  exact (size_add ..).trans (Nat.add_le_add he (show size (step (axisEquiv.symm (u b.1).2.1):Cover) ≤ 1 from le_of_eq (by simp [size,apply_ite Int.natAbs])))
end YM.RG08.Staffer
