import YM.RG08.Yurt.Door
/-! # Offset contribution for actual centered mean & engineering factor.
Apply across all cutoffs. Analytical estimate h horizon. Pre block strengthening. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Yurt
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Quarry Weald Hatch Carrel Laurent Filter RG Precision Exterior Skiff Trickle Steam
open Planned.PrimaryIntegral295 Place Carrier Flint Lagoon
open scoped Classical ContDiff BigOperators Topology ENNReal
variable {I J:Type}{G:Gauge}{n p d e i:ℕ}{D C T B τ η σ δ s:ℝ}{L:Side}
local notation "A" => Loc G 1
-- D deterministic BEFORE scaled gauge coupling replacement, WITH engineering factor.
variable (P:Patch)(K:KernelChoices)(b:Bed)
def spun (S:GrainS (Ed G Cover))(o:Site P.L):GrainS (Ed G Cover):= Trickle.mouth (Prism.rains P K b) (plank P o (flow P.L o S))
def forecast (S:GrainS (Ed G Cover))(h:ℕ):GrainS (Ed G Cover):= (((P.L.val:ℝ)^h)/Fintype.card (Site P.L)) • ∑ o:Site P.L,spun P K b S o
lemma fabled (S:GrainS (Ed G Cover))(o:Site P.L)(e n:ℕ):
 ferry (Cell.plotted P K G b) (S e n) (unitStep P.L) (ahead P.L o) (lift o)=spun P K b S o e n:=by
 funext i f
 unfold spun
 change _=Trickle.brook f (mouth (Prism.rains P K b) (Weald.plank P o (flow P.L o S))) e n i;rw [Trickle.water];unfold Weald.plank Trickle.brook during Forms.raft vat;dsimp only
 rw [b_camp (u:=door P o) (F:=(flow P.L o S e n)) (step_door P o) (fun x P'=> P' f * Forms.design _ x i) (by simp)]
 unfold ferry sonic tote Lagoon.flow Lagoon.tilt;apply tsum_congr;intro t
 simp_rw [flakes,tender,offer,zero_mul,Real.exp_zero,one_mul]
 congr 1;unfold Forms.design;apply Finset.prod_congr rfl;intro j _
 unfold Prism.rains Prism.chill Prism.rightSumKernel Cell.plotted Cell.out
 dsimp only [Pi.add_apply,Pert.Bulk.install,door,Steam.repeatLine,comp_apply,Sum.elim_inl]; rw [add_zero];rfl
lemma grouped (S:GrainS (Ed G Cover)){h0 h:ℕ}(w:0<τ)(C:ℝ)(hC:0≤C)(hv:∀ i,Sings (stance A) h0 w (spun P K b S i e n) C):
 Sings (stance A) h0 w (forecast P K b S h e n) ((P.L.val:ℝ)^h*C):=by
 let c:ℝ:=Fintype.card (Site P.L);have hc:0<c:= Nat.cast_pos.mpr Fintype.card_pos;let a:ℝ:= P.L.val; have ha:0<a:=by unfold a;positivity
 unfold forecast;rw [Pi.smul_apply, Pi.smul_apply, Finset.sum_apply,Finset.sum_apply]
 have he := (Sings.sum univ (a:=fun _=>C) (fun i _=>hv i) (fun _ _=>hC)).smul (a^h/c)
 convert he using 1 -- expense scope
 simp only [sum_const,card_univ,nsmul_eq_mul,abs_of_nonneg (show (0:ℝ)≤a^h/c by positivity)]
 change a^h * C=a^h/c*(c*C);field_simp

/-- Fixed pre demands & assumptions for using trains on all our cutoffs, with constants
 parameters. Notice projection leakage of uncontracted column separate. Export of structural
 test decomposition tagged e=degree. -/
lemma soar (G:Gauge)(l h d e n:ℕ)(s C σ η δ:ℝ)(hη:0<η)(hh:0<σ)(hc:0≤C)(hs:0< s)(hd:h+1≤d)(hr:n≤l+e)(hδ:0≤δ)(hz:δ≤1)(ht:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(hη':2*η ≤ s):∃ D:ℝ,0 ≤ D ∧ ∀ {Q T B V:ℝ}(P:Patch)(K:KernelChoices)(b:Bed)(M:Carrier.Lines P.L)(N:Kernel G.ColorIndex (Loc G 1))(F:GrainS (Ed G Cover)),Odd P.L.val→Tutor P.L s C M G h→Crest P.L M N (Cell.plotted P K G b)→(2*η)/(P.L.val:ℝ)≤δ→ η*(unitStep P.L)≤σ/2→RowCost s P.L N Q →0≤Q→Calls l F→ Permit d l F →0≤T→0≤B→0≤V → Minored G h n (F e n) B →(∀ k≤l+e,Sings (stance _) d hh (F e k) T) →(∀ a<e,∀ k≤l+a,Sings (stance _) d hh (F a k) V) →
 Sings (stance _) d hη (forecast P K b F h e n) (D*T*unitStep P.L+D*(P.L.val:ℝ)^h*((Q+C)^n*V+B)):=by
 obtain ⟨D,hD,H⟩:=trains G l h d e n s C σ η δ hη hh hc hs hd hr hδ hz ht hη'
 refine ⟨D,hD,?_⟩
 intro Q T B V P K b M N F ho hM hE hN hI hw hQ hW hP hT hB hV hS he hm
 have hc':=unitStep_pos P.L
 let u:=unitStep P.L;let a:ℝ:=P.L.val; have ha:0<a:=by unfold a; positivity
 let R:=D*(B+T*u^(h+1)+(Q+C)^n*V)
 have Hx(o): Sings (stance _) d hη (spun P K b F o e n) R:=by
    rw [←fabled];exact H P.L o M N _ _ ho hM hE hN hI hw hQ hW hP hT hB hV hS he hm
 have hu:a^h * (T*u^(h+1))=T*unitStep P.L:=by
    change a^h * (T*a⁻¹ ^ (h+1))=T*a⁻¹;rw [pow_succ,inv_pow];field_simp
 have hh:a^h*R=D*T*unitStep P.L+D*(P.L.val:ℝ)^h*((Q+C)^n*V+B):=by unfold R;unfold a at hu ⊢; linear_combination D * hu
 exact hh ▸ grouped P K b F hη _ (by unfold R u;positivity) Hx
end YM.RG08.Yurt
