import YM.RG08.Pivot.Thicket
/-!
# Analytic lookup on order-diagonal slot kernels

This is NOT expecting the Wicked stencil to represent a whole
nonlinear analytic column: need a lemma on individual Gold slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary Finset
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {R : ℝ} {r n p d j t D : ℕ} {F:Frame G d} {U V : EnvelopeU D R G r}

lemma Sober.jump_null (hf:Sober U)(hp:Polished U){φ:Exam D}(v:Fin r→Potential G)(k:Fin r)(h:∀ i,v i ∈ rangeLt (Axis→G.Color) (n+1))
    (W:E4→G.Color)(hh: W ∈ rangeLt G.Color (n+1)) (he : v k=jump W): Vale.pass U v φ=0 := by
  let g : Cover × Loc G 0→ℝ := fun i=> -scent i.2.2 (W (Place.seat i.1))
  let P x (_:Axis):G.Color:= W x
  obtain ⟨C,hC,hv⟩:= Carrier.royalties (n+1) P (Place.vector_band (fun _ : Axis=>W) (fun _=>hh))
  have hG p : ‖g p‖≤C*dime (n+1) p.1:= by unfold g; rw [norm_neg]; exact (PiLp.norm_apply_le (P (Place.seat p.1) 0) p.2.2).trans (hv p.1 0)
  choose A hA H using fun i=> v_purse (h i)
  unfold pass; apply hf.cover_phi hp k g _ hC hG (fun i=>hA i) H
  funext p; unfold deckP polarP; rw [he]; unfold jump g; simp only [map_sub]; rw [show Place.seat (p.1+step (axisEquiv.symm p.2.1))=Place.seat p.1+basis (heap p).2 from ?_]; abel
  rw [Place.seat_add,Place.seat_step]; rfl
set_option maxHeartbeats 400000 in
lemma pane_shuts (H:Hol G)(hp : Polished U) (hf : Gold U) (hn : ∀ u:Letter F, slot u=r→invest H U u=0): Abates U (d+1) := by
  intro v a hv w hy
  let D':= d; let t:=coinsT D w; let A:=plug t R∘U
  have hb: (∑ i,a i)+cashT w≤d:=by omega
  by_cases h₁ : ∀ i,0<a i
  swap
  · push Not at h₁; obtain ⟨i,hi⟩:=h₁
    have hh:= hv i; rw [show a i=0 by omega, Place.rangeLt,Submodule.mem_bot] at hh
    unfold pass wallet; simp_rw [show ∀ b:Beads _ _, (∏ i,deckP (v i) (b i))=0 from fun b=> Finset.prod_eq_zero (mem_univ i) (by rw [hh]; exact map_zero _),mul_zero]; simp
  have hh (i:Fin r): a i≤d := (single_le_sum (f:=fun i=>a i) (fun i _=>Nat.zero_le _) (mem_univ i)).trans ((Nat.le_add_right ..).trans hb)
  have hz: r ≤ d := (Cases.arity h₁).trans ((Nat.le_add_right ..).trans hb)
  let M:= cook (V:=A) (dapple hf.toToute t) (polished_fun hp _) H d r
  have hu (i:F.Index) (hi : (F.grades i).2=r) (ht : (F.grades i).1+cashT w ≤d): F.coords (basin M) i=0:= by
    let u:Letter F:= ⟨i,w,ht⟩; have he:=inserted H u U; rw [hn u hi, Complex.ofReal_zero, graceT,show (F.grades u.label).2=r from hi] at he
    change 0=F.coords (ladle H A d r) i at he; rw [ladle,dif_pos ⟨dapple hf.toToute t,polished_fun hp _⟩] at he; exact he.symm
  choose Y X hY hX HX using fun i=> Place.generated (v i) (hv i) (hh i)
  have hm := Vale.ply hu X a hX hb hz
  change amount A d r X=0 at hm; rw [rank_launch A (dapple hf.toToute t).toTidy (polished_fun hp _)] at hm
  let P:=fun i=>jump (Y i); let Q := fun i=> sampled (X i)
  have hP i: P i∈rangeLt (Axis→G.Color) (a i) := jump_band (hY i)
  have hQ i: Q i∈rangeLt (Axis→G.Color) (a i) := by rw [show Q i=v i-P i by rw [HX]; unfold P Q; abel]; exact Submodule.sub_mem _ (hv i) (hP i)
  have hx : v=Q+P:= funext fun i=> (HX i).trans (add_comm ..)
  rw [hx,pass_merge hp a Q P hQ hP] -- args?
  refine sum_eq_zero fun i _=> ?_
  by_cases he:i=(fun _=> true)
  · rw [he]; exact (mul_eq_zero.mp hm).resolve_left (by positivity)
  have ht:∃ p, i p=false:= by obtain ⟨p,hp⟩:=Function.ne_iff.mp he; exact ⟨p,Bool.eq_false_iff.mpr hp⟩
  obtain ⟨p,ht⟩:=ht
  refine hf.lucid.jump_null hp _ p (n:=d) ?_ _ (Place.grows _ (Nat.succ_le_succ (hh p)) (hY p)) ?_
  · intro i; split
    · exact Place.grows _ ((hh i).trans (Nat.le_succ _)) (hQ i)
    exact Place.grows _ ((hh i).trans (Nat.le_succ _)) (hP i)
  change (if i p then Q p else P p)=P p; rw [ht]; rfl

lemma invest_less (H:Hol G)(v:Letter F)(hp : Polished U)(ht : Polished V)(h:Toute U)(hx:Toute V) : invest H (U-V) v=invest H U v-invest H V v := by
  rw [sub_eq_add_neg,← neg_one_smul ℝ V,invest_more H _ h (tot_weight hx _) hp (polished_scale ht _),invest_sm H _ _ hx ht]; ring
-- line-on-top using K's own horizontal rows; part convergent.
lemma idle_push (H:Hol G)(Q: Flight j n){x:ℝ}(hx:0<x)(hn:4 ≤ n) (hr:d≤ j)(hv:1/2≤R)(hF: Gold V)(hp:Polished V)
    (hz : ∀ i : Letter F,slot i=r→ invest H V i=0)(u:Letter F)(hu:slot u=r):
    invest H (aboard t (painted G (Carrier.linesOf Q x)) V) u=0 := by
  rw [payout H hv Q hx hn hr hp hF.toToute (pane_shuts H hp hF hz) u (u.bill.trans (Nat.le_succ _)) hu,hz u hu,mul_zero]

end YM.RG08.Pivot
