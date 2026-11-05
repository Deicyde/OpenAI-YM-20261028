import YM.TraceExtension.Terrace.Toil
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price MergeProof.East Further.CorrectedLift Ward Climb Analysis Work Weir
open Further.PhysicalPeriodLimitF933 Shunt PhysicalNext.Repeat.Quince PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells Pressure
open Relay MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}(H:C.Makes)(θ:PostT C.path.levels)(h:G.Simple)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "T!"=> C.path
variable {j k p N v u:ℕ}
lemma win_inc (v u:ℕ) {P:Side}(x:Site P)(hp:v ≤ u):Push.GridApprox.window x v ⊆ Push.GridApprox.window x u:=by rintro _ ⟨Y,h,rfl⟩;exact ⟨Y,box_larger h hp,rfl⟩
lemma wing_inh (v u:ℕ)(hv:u ≤ v)(hp:Push.GridApprox.room (A) j k v):Push.GridApprox.room (A) j k u:=by unfold Push.GridApprox.room at *; linarith only[mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hv) (C.S.a_pos k).le,hp]
lemma backProd (j k N p:ℕ)(hk:j≤k)(hx:k≤N) (a b:Site (C.side j p)) (he:a≠b) (V W:Config G (C.side k p)→ℂ)(u:ℕ)(hP:Interior (Push.GridApprox.window 0 u) V)(hQ:Interior (Push.GridApprox.window 0 u) W) (hR: room (A) j k u):
    pew C.S (hk.trans hx) (C.beta N p) a b (backTo C.path N p hx V) (backTo C.path N p hx W) = Wilson.moment (C.beta N p) (backTo C.path N p hx ((V ∘ pull 1 (anchor C.S p hk a))*(W ∘ pull 1 (anchor C.S p hk b)))):=by
    let l:=({a,b}: Finset (Site (C.side j p))); let n:=C.side k p; let q (F:Config G n→ℂ)(x:Site (C.side j p)):= F ∘ pull 1 (anchor C.S p hk x); let f(x):= if x=a then q V x else q W x
    have hp(F:Config G n→ℂ)(hp:Interior (Push.GridApprox.window 0 u) F)(x:Site (C.side j p)) : Interior (Push.GridApprox.window (anchor C.S p hk x) u) (q F x) := hp.unchanged _ _ (by simpa [affine] using! window_affine (r:=u) 0 (anchor C.S p hk x) 1)
    have hf:= backTo_cells C.path N p hk hx l f u (fun x h=> by unfold f; split_ifs; exacts[hp _ hP x,hp _ hQ x]) hR
    let T:=C.S; have hΩ : backTo C.path N p hx (q V a*q W b)= (backTo C.path N p hx V ∘ Lattice.translate (anchor T p (hk.trans hx) a))*(backTo C.path N p hx W ∘ Lattice.translate (anchor T p (hk.trans hx) b)):=by
        simp only [l,Finset.mem_singleton,he,not_false_eq_true,Finset.prod_insert, Finset.prod_singleton, f,if_true, if_neg he.symm] at hf
        unfold q at *; rw [backTo_orient (F:=V) C.path N p hk hx a 1 (cylinder_env hP),backTo_orient (F:=W) C.path N p hk hx b 1 (cylinder_env hQ)] at hf
        simp only [Function.comp_apply,pull_one] at hf; exact hf
    exact congr_arg _ hΩ.symm
lemma Broom (j k N p:ℕ)(hk:j≤k)(hx:k≤N)(V:Config G (C.side k p)→ℂ) (u:ℕ)(hP:Interior (Push.GridApprox.window 0 u) V)(hR: room (A) j k u):Interior ((tilesAt C.S p (hk.trans hx)).chamber 0) (backTo C.path N p hx V):=by
   have h : Interior (Push.GridApprox.window (anchor C.path.S p hk 0) u) V:= by rw[show anchor C.path.S p hk 0=0 from (C.S.toDepth hk p).root.map_zero]; exact hP
   exact (backTo_local C.path N p hk hx 0 u h).enlarges (room_fits p (A) u hk hx hR 0)
lemma differ (j k N p:ℕ)(hk:j≤k)(hx:k≤N) (a b: Site (C.side j p))(V W X:Config G (C.side k p)→ℂ)(h₂:Envelope V)(h₃:Envelope W)(h₀:Envelope X) : let w(g):= pew C.S (hk.trans hx) (C.beta N p) a b (backTo C.path N p hx g) (backTo C.path N p hx X)
    w V = w W + w (V-W):=by
   intro w; let β:= C.beta N p; let f := fun (V:Config G (C.side k p)→ℂ)(a:Site (C.side j p))=> (backTo C.path N p hx V) ∘ Lattice.translate (anchor C.S p (hk.trans hx) a)
   let q g:= f g a*f X b
   have hz : q (V-W)= q V-q W:=by
       have hv:Envelope (V-W):= Cask.envUsub h₂ h₃
       have hP:=backTo_add C.path N p hx (F:=V-W) hv h₃; rw [sub_add_cancel] at hP
       ext1 U; dsimp only [q,Pi.mul_apply,f,Function.comp_apply,Pi.sub_apply]; rw[hP,Pi.add_apply]; ring
   let p'(g:Config G (C.side k p)→ℂ)(e:Envelope g):= backTo_env C.path N p hx e
   let L:= law G (C.side N p) β
   have hv(v:Config G (C.side k p)→ℂ)(e:Envelope v): Integrable (q v) L:=by
       have hp(v:Config G (C.side k p)→ℂ)(e:Envelope v)(x): Envelope (f v x):=(p' v e).comp_env (show Continuous (Lattice.translate _ : Config G (C.side N p)→_) by unfold Lattice.translate; fun_prop).measurable
       have he:= Cask.envUmul (hp v e a) (hp X h₀ b); exact Cask.capped he L
   change Wilson.moment β (q V) = Wilson.moment β (q W) + Wilson.moment β (q (V-W)); rw [hz]; unfold Wilson.moment; simp_rw[Pi.sub_apply];rw[integral_sub (hv _ h₂) (hv _ h₃)];ring
end YM.Trace.Terrace
