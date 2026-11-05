import YM.UVExtension.Steady.CinemaRows
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Stove

/-! Core responses in comparison. V at probes may vary, so
 do not use free-open-branch in supplied allocations. Signal arithmetic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f:Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {R:ι→ PathData G} {σ σ':ℝ} {g:PathData G}
structure Concerted (v: Filter ι)(T : ι→ Tube G S): Prop where
     cap : ∃ σ g,Revenues v σ (fun n=> (T n).up) g
     cap' : ∃ σ g,Revenues v σ (fun n=>(T n).down) g
     high : ∃ c,∀ i, (T i).high=c
     low : ∃ c,∀ i,(T i).low=c
     leaps : ∀ i j k, ∃ r,Tendsto (fun n=> (T n).R.mf i j k) v (𝓝 r)
     qui : ∀ i j k, ∃ r,Tendsto (fun n=> (T n).R.mn i j k) v (𝓝 r)
     ore : ∀ i j k, ∃ r,Tendsto (fun n=>(T n).R.o i j k) v (𝓝 r)
namespace Concerted
variable {qq: Filter κ} {T:ι→ Tube G S}(p:Concerted v T) {t:κ→ Bool→ ι} (h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:κ→ E} {k:ℕ} {d:ℝ} {U:κ→ E→ Config G n} {V:κ→ E→ Config G c}
variable (P:ℕ)(he:∀ᶠ i in qq,Mode (V i) (x i) k d)
include p h he
lemma xn (P:ℕ)(w:Twin c): Walt qq x k (fun i b z=> (T (t i b)).Xn P (V i z) w):=by
    obtain ⟨σ,u,hσ⟩:= p.cap'; obtain ⟨q,hq⟩:= p.low; simp_rw [Tube.Xn,hq]; exact queries he _ (fun b=> hσ.incurs (h b)) P _ q S.patch.L.property w
omit he
lemma xf {U:κ→ E→ Config G f}(Hp:∀ᶠ i in qq,Mode (U i) (x i) k d) (P:ℕ)(w:Twin f): Walt qq x k (fun i b z=> (T (t i b)).Xf P (U i z) w):=by
    obtain ⟨σ,u,hσ⟩:= p.cap; obtain ⟨q,hq⟩:= p.high; simp_rw [Tube.Xf,hq]; exact queries Hp _ (fun b=> hσ.incurs (h b)) P _ q (by norm_num) w
omit p h
lemma ponder (p: Site n) (g:Walk)(Hp:∀ᶠ i in qq,Mode (U i) (x i) k d) (b:κ→Bool→ℝ)(hb:Together qq b)(s:Bool)(u:κ→Bool→ E→ G.Color)(h: Walt qq x k u) : Walt qq x k (fun i j z=> receive (rated (U i z) p g (b i j)) s (u i j z)):=by
    let L (i:κ)(z:E) := receive (rated (U i z) p g 1) s
    let f x i (_:Bool) z:= L i z (dot G x)
    have hv y : Walt qq x k (f y):=by
       refine Walt.twin (|(1:ℝ)| * (royalty G ^2* ‖dot G y‖)) (2*g.length*d*royalty G+1) ?_; filter_upwards [Hp] with i hi
       exact ⟨shortenWalk (R:=g.length) g p 1 le_rfl (Brush.certified zero_le_one (dot G y)) hi.atLink s,rfl⟩
    let w x' i b z:= (u i b z) x'
    have hw x' : Walt qq x k (w x'):=h.leaf ((LinearMap.comp (LinearMap.proj x') (WithLp.linearEquiv 2 ℝ _).toLinearMap : G.Color →ₗ[ℝ] ℝ).toContinuousLinearMap)
    refine ((Walt.stamp hb).pay (Walt.schedule univ (fun j n b y=> w j n b y • f j n b y) (fun j _=> (hw j).pay (hv j)))).same ?_
    filter_upwards with i j; filter_upwards with z
    let X:=u i j z; have ht : ∑ y,w y i j z • f y i j z=L i z X := by
        unfold f; simp_rw [← map_smul, ← map_sum]; rw [show ∑ y,w y i j z • dot G y=X from (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr _]
    have hT : receive (rated (U i z) p g (b i j)) s=(b i j) • L i z:= by unfold L receive rated; cases s <;> simp
    change _= _ • ∑ y,w y i j z • f y i j z; rw [ht, hT]; rfl
lemma behold {J: Type}(P:Finset J)(L: J→κ→Bool→ E→ Pressure.Pay G)(g:Bool)(w:κ→Bool→ E→ G.Color)(h:∀ t∈P,Walt qq x k (fun i b z=> receive (L t i b z) g (w i b z)))(hp:∀ (i:κ) b z j,j∉P→ L j i b z=0): Walt qq x k (fun i b z=> receive (∑' t,L t i b z) g (w i b z)):=by
   apply (Walt.schedule _ (fun t i b z=> receive (L t i b z) g (w i b z)) h).same; filter_upwards with i b; filter_upwards with y; rw [tsum_eq_sum (hf:=hp i b y)]
   unfold receive; cases g <;> simp
include p h he
lemma reach (w:Twin f)(z:Twin c)(D:ℕ) (g:Bool) {u:κ→Bool→ E→ G.Color} (ht:Walt qq x k u): Walt qq x k (fun i b y=> receive ((T (t i b)).Φ D (V i y) w z) g (u i b y)):=by
    let r:= S.ratio.residue (mesh w).1; let m:= S.patch.L.val; let j (i:Cover):= route (lift r) (m • i) 1
    have hi : Injective j := by intro i l hh; have H : m • i=m • l := Eq.trans (route_end _ _ 1).symm ((congr_arg (stop (lift r)) hh).trans (route_end ..)); exact (smul_right_injective _ S.patch.L.property.ne') H
    let v:= bought_walk D j hi
    refine behold v.toFinset (fun k i b y=> casted S (T (t i b)).R D (V i y) (mesh w) (mesh z) k) g u ?_ ?_
    · intro k hk; unfold casted; dsimp only; split_ifs
      next hk=>
        obtain ⟨c,hc⟩:= p.leaps (r,(mesh w).2) (mesh z).2 k; exact ponder _ _ (U:=fun i z=>replica S.ratio (V i z)) (he.mono fun i hi=>⟨hi.pos,recopy S hi.atLink⟩) _ (pairsHere _ c (fun b=>hc.comp (h b))) g u ht
      next hk=> unfold receive; cases g <;> simp <;> apply Walt.ready
    intro i b y k hk; exact if_neg (fun h=> hk (v.mem_toFinset.mpr h.1))
omit p
lemma extensionP {K:ι→Row α β}(p:∀ i j k,∃ r,Tendsto (fun n=>K n i j k) v (𝓝 r))(u:Co c α)(z:Co c β) (M D:ℕ)(hD:0<D)(g:Bool){w: κ→Bool→ E→G.Color}(hp:Walt qq x k w) : Walt qq x k (fun i b y=> receive (lane M D (V i y) (K (t i b)) u z) g (w i b y)):=by
    let j (i:Cover):= route 0 i 1
    have hi : Injective j := fun i j he=> Eq.trans (route_end 0 i 1).symm ((congr_arg (stop 0) he).trans (route_end 0 j 1))
    let s:= bought_walk M j hi; refine behold s.toFinset (fun k i b y=> priced M D (V i y) (K (t i b)) u z k) g w ?_ ?_
    · intro k hk; unfold priced; split_ifs
      next h'=> obtain ⟨c,hc⟩:=p u.2 z.2 k; exact ponder _ (j k) he _ (pairsHere _ c (fun b=>hc.comp (h b))) g w hp
      next h'=> unfold receive; cases g <;> simp <;> apply Walt.ready
    intro i z y k hk; refine if_neg (fun H=> hk (s.mem_toFinset.mpr ((le_mul_of_one_le_right (Nat.zero_le _) hD).trans H.1)))
end Concerted
end YM.UVExtension.Steady
