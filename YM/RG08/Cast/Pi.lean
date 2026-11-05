import YM.RG08.Cast.Indent

/-! # Cofinal arithmetic of effective tensors, sym & signed -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cast
open Lattice Laurent Forms Pert.Bulk Isles Packets Carrel Filter Finset Function RG
open Anchor Rudder Rudder.Symmetry Exterior Stationary Bloch RG08.Flat Spar Next.Free
open scoped Topology ContDiff Classical BigOperators ENNReal Matrix
variable {I:Type}{n k:ℕ}{σ C:ℝ}{P:Side}

lemma readNTend {F:Flake k (Market I)}{τ B:ℝ}(hp:Held (carpet _) τ B F)(hs:0≤τ)(i:Fin k)(x:Tape k (Market I)){N:ℕ→Side}(h:Tendsto (fun j=>(N j).val) atTop atTop):
    Tendsto (fun j=>pour F i (port (N j) ∘ x)) atTop (𝓝 (F x)):=by
 let U(w:Tape k (Market I)):= if w=x then F w else 0
 have he(a:Market I):∀ᶠ j in atTop,reach (port (N j) a)=a:=(eventually_unfold N h a.1).mono fun j hj=>by unfold reach port;rw [hj]
 have ht(w):Tendsto (fun j=> (Isles.lantern i (port (N j) ∘ x)).indicator F w) atTop (𝓝 (U w)):=by
    apply Filter.EventuallyEq.tendsto
    filter_upwards [eventually_all.mpr (fun i=>he (w i)),eventually_all.mpr (fun i=>he (x i))] with j hw hx
    have hf:w∈Isles.lantern i (port (N j) ∘ x) ↔ w=x:=by
      constructor
      · intro H;ext i:1;rw [←hw i,←hx i];exact congrArg reach (found H i)
      rintro rfl; exact ⟨(hx i).symm,rfl⟩
    rw [Set.indicator_apply];dsimp only [U];simp_rw [hf]
 let T (w:Tape k (Market I)):= if w i=x i then |F w| else 0
 have hh :∀ᶠ j:ℕ in atTop, ∀ w, ‖(Isles.lantern i (port (N j) ∘ x)).indicator F w‖ ≤ T w:=by
    filter_upwards [he (x i)] with j hk
    intro w
    by_cases hy:w i=x i
    · dsimp only [T];rw [if_pos hy]; unfold Set.indicator;split_ifs<;>simp
    · have hg:w∉Isles.lantern i (port (N j) ∘ x):=fun hz=>hy (((Set.mem_setOf.mp hz).1).trans hk)
      dsimp only [T];rw [Set.indicator_of_notMem hg,if_neg hy,norm_zero]
 have hu:=tendsto_tsum_of_dominated_convergence (cell_sum hp hs i (x i)) ht hh
 simpa only [pour,U,tsum_ite_eq] using hu

lemma peepers {F V:Flake k (Market I)}{τ C D:ℝ}(hp:Held (carpet _) τ C F)(h':Held (carpet _) σ D V)(ht:0<τ)(hs:0<σ)(i:Fin k){N:ℕ→Side}(he:Tendsto (fun j=>(N j).val) atTop atTop)(h:∀ j:ℕ,pour (P:=N j) F i=pour V i):F=V:=by
 funext j
 have hv:=readNTend hp ht.le i j he;have hh:=readNTend h' hs.le i j he
 simp_rw [h] at hv; exact tendsto_nhds_unique hv hh

private lemma arcade_symm {G:Gauge}{M:Matrix (Body n P) (Body n P) ℝ}(h:M.transpose=M): Forms.Sym (arcade (G:=G) M):=by
 intro ξ;ext x
 have hM (i j:Body n P):M i j=M j i:= (congrFun (congrFun h i) j).symm
 let u:Fin 2:=(Fin.succ 0)
 have hx:ξ u≠ ξ 0:=ξ.injective.ne (by decide)
 rcases eq_or_ne (ξ 0) 0 with h0|h0
 · have hp:ξ u=u:=by rw [h0] at hx; generalize hv:ξ u =a at *; fin_cases a <;> first | exact (hx rfl).elim| rfl
   simp only [woven,arcade,Function.comp_apply,h0,show ξ (Fin.succ 0)=_ from hp];rfl -- maybe solved
 have hv:ξ 0=u:=by generalize he:ξ 0=v at *;fin_cases v <;> first | exact (h0 rfl).elim| rfl
 have hh:ξ u=0:=by rw [hv] at hx;generalize he:ξ u=v at *;fin_cases v <;> first| rfl|exact (hx rfl).elim
 simp only [woven,arcade,Spar.shaded,Matrix.of_apply,Function.comp_apply,hv,show ξ (Fin.succ 0)=_ from hh];rw [hM ((x u).1,(x u).2.1),eq_comm (a:=(x u).2.2)]

lemma dressed_symm {G:Gauge}{D:Kernel (TypeFace 2) (TypeFace 2)}{C τ:ℝ}{N:ℕ→Side}
     {M:∀ i,Matrix (Body 2 (N i)) (Body 2 (N i)) ℝ}(hp:Tendsto (fun i=>(N i).val) atTop atTop)
     (hx:∀ i,Matches D (M i))(hM:∀ i,(M i).transpose=M i)(h:city 1 D)(he:RowCost τ 1 D C)(hs:0<τ)(hc:0≤C) :
     Forms.Sym (beam G D):=by
 let F:=beam G D
 have H:=spur_cost (G:=G) he (from_row D h he) hc hs.le
 have hb:=spur_path (G:=G) h
 have hh: Sym (spur G D):=by
    intro e
    apply peepers (H.perm _) H hs hs 0 hp (fun i=>?_)
    rw [←Carrel.ordered _ _ _ hb,spur_matches (hx i), arcade_symm (hM i)]
 intro e;funext x
 have ht (x:Tape 2 (Market (Tone G.ColorIndex))):permitted Cover G.ColorIndex 2 x→permitted Cover G.ColorIndex 2 (x ∘ e):=fun h i=>h (e i)
 have hX:permitted Cover G.ColorIndex 2 (x ∘ e)↔permitted Cover G.ColorIndex 2 x:=⟨fun h i=>by simpa using h (e.symm i), ht _⟩
 unfold woven beam Anchor.extend
 by_cases he:permitted Cover G.ColorIndex 2 x
 · rw [dif_pos he,dif_pos (hX.mpr he)] -- order?
   exact congrFun (hh e) (fun i=>decoded Cover G.ColorIndex 2 (x i) (he i))
 rw [dif_neg he,dif_neg (mt hX.mp he)]

end YM.RG08.Cast
