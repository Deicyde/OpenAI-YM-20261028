import YM.RG08.Flat.Agreement

/-!
# Linear history on *same* blocking and threshold schedule

Alter clip factorization only to instantiate the separate linear library (keeping everything
that enters `levels.clock.op` definitionally, in particular Patch, smoothing levels, and kernel
penalty). The evaluated Hessian is unchanged: equality theorem below. Can derive the UV rate for
the *actual* flat precision this way, after the formal-specific length/delay choices, without a
hypothesis that arbitrary clips from `C` happened to meet the entrance asks of a separate
`retained_support` call. Does NOT identify Beds or ANY higher-order data produced using changed
clips. This is a factorization used to prove an estimate, not a change of regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG08.Rate RG Precision Next.Free Exterior
open scoped Topology ENNReal
variable {G : Gauge}

def rearrange (S : Stage) (x : ℝ) (hx : 0 < x) : Stage :=
 {S with clip:= ⟨x,x/32,S.clip.relaxation,hx,by positivity,by linarith,S.clip.radius_pos⟩,
         slow_selector:=S.slow_selector}

def adjust (a : Levels G) (γ : ℕ→ℝ)(hg:∀ i,0<γ i) : Calendar G :=
 {a.clock with stage:=fun i=> rearrange (a.clock.stage i) (γ i) (hg i)}

variable (a : Levels G) (γ : ℕ→ℝ)(hg:∀ i,0<γ i)

def shadow : Levels G where
  clock := adjust a γ hg
  fits := {
     mesh := a.fits.mesh
     sameFactor := a.fits.sameFactor
     monotoneL := a.fits.monotoneL
     mono := a.fits.mono
     stepSlow := a.fits.stepSlow
     deep := a.fits.deep
     deepOrder := a.fits.deepOrder
     deepPower := a.fits.deepPower
     deepExp := a.fits.deepExp
     delayed := a.fits.delayed
     smallField := a.fits.smallField
     sizeT := a.fits.sizeT
     fitsPatch := a.fits.fitsPatch
     thetaRange := a.fits.thetaRange
     thetaMono := a.fits.thetaMono
     driftSmall := a.fits.driftSmall
     logCost := a.fits.logCost }
  blocks m p := by obtain ⟨h,hg,hx⟩:= a.blocks m p; exact ⟨h,hg,hx⟩

theorem same_shadow {P R : MapPrices} {H : Horizon a}{T : Horizon (shadow a γ hg)}(h:H.Suffices P)(ht:T.Suffices R)(N i:ℕ)(hI:i ≤ N): output (H.H N i)=output (T.H N i):= by
  have he j m (h₁:m ≤ N)(h₂:N=m+j)(t) :
      quadratic (H.H N m) (a.S.side m t)=quadratic (T.H N m) (a.S.side m t) := by
    induction j generalizing m with
    | zero => rw [show m=N by omega,same_terminal h,same_terminal ht]
    | succ j hj =>
      have hM : m<N := by omega
      let a':= shadow a γ hg
      have hP := poised (h.crossings _ _ t hM).trial (T:=installed (a.clock.op m t).ratio (H.towers N m).A0) (W:=installed (a'.clock.op m t).ratio (T.towers N m).A0) (Y:=((T.H N (m+1)).metric.acts (a.S.side (m+1) t))) (Y':=(T.H N m).metric.acts (a.S.side m t))
        (ht.crossings N m t hM).trial (ht.all N (m+1) hM _).symmetric.1 (ht.all N m hM.le _).symmetric.1
      symm
      apply sub_eq_zero.mp
      apply hP.trans
      -- Column side still a.Levels shadow -- `change` first arg
      have hv := hj (m+1) hM (by omega)
      unfold quadratic at hv
      unfold Levels.S at hv
      unfold Levels.S
      rw [← hv, sub_self,Matrix.mul_zero,Matrix.zero_mul] -- match?
  have uses {a:Levels G}{B:Horizon a}{P}(h:B.Suffices P):
      RowCost 0 1 (output (B.H N i)) (sumToken*(Fintype.card Faces*(P.Ω (a.clock.J i)))) ∧
       ∀ n,Matches (output (B.H N i)) (quadratic (B.H N i) n) :=
    output_cost (fun x y=> ((h.rows N i hI).2.1 x y).mono (P.alpha_pos _).le le_rfl) (Ω_pos h i) le_rfl zero_le_one
  exact readahead (t:=a.S.side i) (mesh_sides a.S i) (uses h).1 (uses ht).1 le_rfl le_rfl (fun t=>(uses h).2 _) (fun t=> he (N-i) i hI (by omega) t ▸ (uses ht).2 _) -- precedence ▸
end YM.RG08.Flat
