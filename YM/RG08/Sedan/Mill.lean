import YM.RG08.Sedan.Ovals
import YM.RG08.Forms.Coherent
/-! # Cap/wind of all charts. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sedan
open Filter Function Matrix MeasureTheory Finset Lattice Exterior Wilson RG Precision Stationary Work.F05 Tree Carrel Prism Tack Camera Gallery
open Forms Rudder Anchor Isles Laurent Pert.Bulk Packets Mount Glyph Room Bloch Quarry Aggregate Steam Spar Symmetry Roost
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal Matrix.Norms.Frobenius
variable {c:Side}{G:Gauge}{P:Patch}{K:KernelChoices}{I J:Type}{n:ℕ}

lemma raft_symm (F: Flake n I)(m:I→J→ℝ) (hs:Forms.Sym F): Forms.Sym (Forms.raft (repeatLine m n) F):=by
 intro i;funext x
 let e:= Equiv.arrowCongr i (Equiv.refl I)
 change (∑' t,F t * ∏ j,m (t j) ((x ∘ i) j))=∑' t,F t*∏ j,m (t j) (x j)
 rw [←e.symm.tsum_eq] -- convert lhs t=t∘i
 apply tsum_congr;intro z; rw [show e.symm z=z ∘ i from rfl,show F (z ∘ i)=F z from congrFun (hs i) z];congr 1; exact Equiv.prod_comp i (fun j=>m (z j) (x j))

private lemma tranpair (Γ:Kernel I I){q p n:ℕ}{F:Flake (q+1) (Market I)}{A:Flake (p+1) (Market I)}(hg:city 1 Γ)(h:Cohort F)(hA:Cohort A): Cohort (Steam.pair Γ F A n):=by
 unfold Steam.pair;split;next he=> subst n;exact (h.bridge' hA hg).smul _
 exact fun _ _=>rfl
lemma scoured {A:Grain (Market I)}(Γ:Kernel I I)(he:city 1 Γ)(h:legal A)(x:ℕ): legal (burn Γ A x):=by -- remove e n
 induction x using Nat.strong_induction_on with
 | h x ih=>intro k n;cases x with
   | zero=>rw [spark]; apply h
   | succ x=>
     refine ⟨?_,coal Γ A _ _ _⟩;rw [blaze];apply Cohort.smul; unfold wheels; refine (Cohort.add ?_ ?_)
     · apply Cohort.smul;exact ((ih x (Nat.lt_succ_self _) k (n+2)).1.lap' he)
     refine Cohort.sum _ _ (fun i _=>Cohort.sum _ _ fun j hj=> Cohort.sum _ _ fun a _=> ?_)
     have hj:j ≤ x:=by simpa using hj
     apply tranpair Γ he (ih _ (by omega) a _).1 (ih _ (by omega) _ _).1
private lemma raft_nil (m:I→J→ℝ):Forms.raft (repeatLine m n) 0=0:=by ext;simp [Forms.raft,Forms.vat]
lemma mechanical {A:Grain (Market I)}(Γ:Kernel I I)(m:Kernel I J)(h:city 1 Γ)(hp:city 1 m)(ha:Steam.Eligible A)(he:legal A): Eligible (Steam.allG Γ A m) ∧ legal (Steam.allG Γ A m):=by
 let F:=Steam.allG Γ A m
 have ht(k n) :Forms.Sym (Steam.cinder Γ A 1 k n):=Mount.Sym.sum _ _ (fun j _=>(scoured Γ h he (j+1) k n).2.smul _)
 have hy(k n):Cohort (Steam.cinder Γ A 1 k n):=Forms.Cohort.sum _ _ (fun j _=>(scoured Γ h he (j+1) k n).1.smul _)
 refine ⟨?_,fun k n=>⟨((he k n).1.raft' (fun _=>hp)).add ((hy k n).raft' (fun _=>hp)), (raft_symm _ _ (he k n).2).add (raft_symm _ _ (ht k n))⟩⟩
 have hQ e n (hv:F e n≠0):0<e∧n ≤ e+2∧Even (e+n):=by
    by_contra H
    have hx (V:Grain (Market I))(hs:Eligible V):V e n=0:=by
       by_contra hL
       exact H ⟨Nat.pos_of_ne_zero (fun hz=>by rw [hz,hs.dark] at hL;exact hL rfl),hs.head _ _ hL,hs.foot _ _ hL⟩
    have hC : Steam.cinder Γ A 1 e n=0:= Finset.sum_eq_zero fun j _=>by rw [hx _ (live ha _),smul_zero]
    exact hv (by unfold F Steam.allG Steam.strict;rw [hC,hx A ha,raft_nil,add_zero])
 exact ⟨funext (fun i=> Classical.not_not.mp fun hv=>Nat.lt_irrefl 0 (hQ 0 i hv).1),fun _ _ hv=>(hQ _ _ hv).2.1,fun _ _ hv=> (hQ _ _ hv).2.2⟩
variable (h:P.Branches K G){C:Castle G}(Z:ChartRatio G)(A:Bed)
lemma fortune (hC:Mount.Stable C){σ p:ℝ}(hT:Cell.Warm G K P A σ p)(ht:0<σ)(hv:σ ≤ 1): Grimoire (mill G P K h C Z A)∧ mill G P K h C Z A 0=0:=by
 obtain ⟨he,hp⟩:=Prism.ready_roads P K A hT ht hv
 let X:=inlet h C Z;have hE:=inlet_eligible h Z hC; have hh:=legal_inlet h Z hC
 obtain ⟨hu,hb⟩:=mechanical _ _ he.city hp.city hE hh
 refine ⟨⟨fun i k hl=>⟨hu.head i k hl,hu.foot i k hl⟩,hb,?_⟩,hu.dark⟩
 intro e n
 have hS k:slaw X k:=by
   by_cases he:0<k
   · have hd:=((castle_room P C hC k).add (bell_room h k)).neg.add (dusk_room P Z k)
     intro n; convert hd n using 1;rw [show X k n=ghost h C Z k n by unfold X inlet;rw [if_pos he]];rfl
   intro n;refine ⟨1,0,zero_lt_one,le_rfl,?_⟩;unfold X inlet; rw [if_neg he];exact zero_held
 obtain ⟨α,hA,hV⟩:=hedgeline X e hE hh hS
 let θ:=min σ α;have hθ:0<θ:=lt_min ht hA
 have hw:Isles.seats θ (fun i=>unveil (hedge e X) (Isles.chain i)) (hedge e X):=fun j k=>by obtain ⟨B,H⟩:=hV j k;exact ⟨B,H.mono hθ (min_le_right ..) le_rfl⟩
 obtain ⟨b,H⟩:=cooling hw (((Isles.tagged he ht).mono hθ (min_le_left ..) le_rfl).line) ((Isles.tagged hp ht).mono hθ (min_le_left ..) le_rfl) e n
 refine ⟨_,_,hθ,H.cost,?_⟩
 unfold mill;rw [←all_hedge _ _ n e le_rfl]; exact H.palm
end YM.RG08.Sedan
