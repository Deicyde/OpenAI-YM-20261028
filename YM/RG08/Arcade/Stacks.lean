import YM.RG08.Arcade.Stars
/-!
# Horizon restriction of the graded jets. It is parametric in the same field stencil dictionary. Applies also to pivot leading.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Arcade
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages Drift Spin
open WardBin
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ} {H:Hol G}
section engineered
private lemma directly {I:Type*} [Fintype I] {E:I→Type*} [∀ i, NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] {f g: ℝ → ∀ i,E i}
  (h: ∀ i, WardBin.leading k (fun x=> f x i)=WardBin.leading k (fun x=>g x i)) (hf:ContDiffAt ℝ k f 0) (hg:ContDiffAt ℝ k g 0) : iteratedFDeriv ℝ k f 0=iteratedFDeriv ℝ k g 0 := by
    have hp (i:I) (f:ℝ → ∀ i,E i)(hf:ContDiffAt ℝ k f 0):
        leading k (fun x=> f x i) = (k.factorial:ℝ)⁻¹ • (iteratedDeriv k f 0) i:= by
       let T: (∀ i,E i)→L[ℝ] E i:= ContinuousLinearMap.proj (φ:=E) i
       exact congr_arg ((k.factorial:ℝ)⁻¹ • · : E i→E i) (DFunLike.congr_fun (ContinuousLinearMap.iteratedFDeriv_comp_left (E:=ℝ) T hf le_rfl) (fun _:Fin k=>(1:ℝ)))
    have hz : iteratedDeriv k f 0=iteratedDeriv k g 0:= funext fun i=> smul_right_injective (E i) (show (k.factorial:ℝ)⁻¹≠0 by positivity) ((hp i f hf).symm.trans ((h i).trans (hp i g hg)))
    apply ContinuousMultilinearMap.ext; intro x; rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,hz]
private lemma itsvalue (G:Gauge)(d j:ℕ)(p:Snap G d) (i:Fin (j-1)) : linksH G d j p i=Drops.expand d p i.val := rfl
lemma leading_H (J:Jet G)(_hx:d≤j)(he:k≤d): let v t:= engineered t (trunk d J); let u t:= engineered t (trunk j J); let A:= linksH G d j
    iteratedFDeriv ℝ k (A ∘ v) 0=iteratedFDeriv ℝ k u 0:= by
    intro f g A; have ht:ContDiffAt ℝ k (A ∘ f) 0 := (A.contDiff.contDiffAt).comp _ ((eng_cont (trunk d J) _).contDiffAt)
    have hg:ContDiffAt ℝ k g 0 := (eng_cont (trunk j J) _).contDiffAt
    refine directly (E:=fun i:Fin (j-1) => Taylor G i.val) (f:=A ∘ f) (g:=g) ?_ ht hg
    intro i; let n:= i.val+2
    have hz : (fun x=> g x i)= (fun t:ℝ=> t^n • J i.val):=rfl
    by_cases h:i.val<d-1
    · rw [show (fun x=> (A∘ f) x i)=(fun x=>g x i) from funext fun x=>?_]
      change Drops.expand d (engineered x (trunk d J)) i.val= _; rw [Drops.expand,dif_pos h]; rfl
    rw [hz, lead_monomial,if_neg (by unfold n; omega)]
    have hv(y:ℝ): (A ∘ f) y i=0:= by unfold Function.comp A; rw [itsvalue,Drops.expand,dif_neg h]
    rw [funext hv,leading_zero_iff]; simp

set_option maxHeartbeats 600000 in
lemma leading_scope (G:Gauge)(M:Tensor.T (Snap G d) ℂ l)(N:Tensor.T (Snap G j) ℂ l)(hp: d ≤ j)(hm:∀ x,M x=N ((linksH G d j) ∘ x))(he:k≤d) : tile M k=tile N k := by
    apply eval_ext; intro V
    let u (t:ℝ):= engineered t (trunk d V); let v:= linksH G d j ∘ u; let w (t:ℝ):=engineered t (trunk j V); let f:=Tensor.diagonal N; let g:=Tensor.diagonal M
    have h:= Work.G05.jets_comp (f:=v) (d:=d) ((linksH G d j).contDiff.contDiffAt.comp _ ((eng_cont (trunk d V) _).contDiffAt)) (f':=w) ((eng_cont (trunk j V) d).contDiffAt) (g:=f) (g':=f) ((Tensor.diag_smooth N d).contDiffAt) ((Tensor.diag_smooth N d).contDiffAt) (by unfold v u w; simp [Parts.engineered_zero]) (fun i hi=>leading_H V hp hi) (fun _ _=>rfl) k he
    rw [← tile_reads, ← tile_reads, show (fun t=>Tensor.diagonal M (engineered t _)) = f ∘ v from ?_]; swap
    · exact funext fun t=> hm (fun _=>u t)
    unfold leading iteratedDeriv
    exact congr_arg (fun (P:Tensor.T ℝ ℂ k)=> (k.factorial:ℝ)⁻¹ • P (fun _=>1)) h
end engineered
section frame
variable (F:Labels.Frames G)(hp:d≤j)(H:Hol G)
lemma spark_grade (i:ℕ)(hi:i≤d)(hx:n≤d) (V: Shale (Loc G 1) r): let q:= ladle H V d l; let p:= ladle H V j l
    gradePart (i,n) p=raiseLabel G hp (gradePart (i,n) q) := by
    intro Q P; by_cases h:Dappled V∧Polished V; swap; · unfold P Q ladle; simp [h]
    apply Subtype.ext; change _=(gradePart _ Q).val; unfold Q P ladle
    rw [dif_pos h,dif_pos h, basin_tile _ (hi.trans hp) (hx.trans hp), basin_tile _ hi hx]; split; next hv=>
       subst n; apply Eq.symm; refine leading_scope G _ _ hp (fun x=>?_) hi
       rw [shade_all,shade_all]; exact congr_arg (fun t:ℝ=> ((↑((l.factorial:ℝ)⁻¹ * t) : ℂ))) (cash_le V h.1.toTidy h.2 H hp x)
    next h'=> rfl
lemma coordinates_restrict (i: (F.level d).Index)(n)(V : Shale (Loc G 1) r) : (F.level j).coords (ladle H V j n) (sequel F hp i)=(F.level d).coords (ladle H V d n) i:= by
    let g := (F.level d).grades i; rw [Film.costs_only _ (sequel F hp i), relayV, show gradePart g (ladle H V j n)=_ from spark_grade hp H g.1 ((F.level d).bound i) (Film.second_fits ..) V, earned_coord, ← Film.costs_only _ i] -- implicit param
variable {U:BoardU D R G}
def trim (p: Native (Letter (F.level j))): Native (Letter (F.level d)):= fun i=> p (this_letter F hp i)
theorem scopeC (U:BoardU D R G) : call H (F.level d) U=trim F hp (call H (F.level j) U) := by
    ext1 b; unfold call trim; ext e; rw [PowerSeries.coeff_mk,PowerSeries.coeff_mk,auditT,auditT,slotUP]
    apply sum_congr rfl; intro i _; split
    next h=>
       unfold invest graceT; rw [show (this_letter F hp b).label=sequel F hp b.label from rfl, relayV, coordinates_restrict]; rfl
    next h=> rfl
end frame
end YM.RG08.Arcade
