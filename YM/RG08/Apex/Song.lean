import YM.RG08.Apex.Bear
/-! # Limit Ward and Partial invariant chart matching -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Summit
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums UVExtension.Free
open scoped BigOperators Topology Real Classical
open Chain Wings
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g:KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}
variable {I : Type} {u : I→Windows} {r e j s : ℕ}

private abbrev Bus (G : Gauge) (n : ℕ) (m : Side) := (i : Fin (n+1))→ Tensor.T (Link G m) ℝ i.val
private def gates (G : Gauge) (n : ℕ)(m : Side) : Submodule ℝ (Bus G n m) where
   carrier := {x| ∃ f:Link G m→ℝ,Pointwise f∧ ∀ i,Tensor.coeff f i.val 0=x i}
   zero_mem' := by
     refine ⟨0,?_,?_⟩; · simpa using! (Pointwise.coin (F:=WilsonQ G m) Wilson_witness 0)
     exact fun i=>Tensor.coeff_zero _ _
   add_mem' := by
     rintro _ _ ⟨h,hp,hv⟩ ⟨f,he,hF⟩; exact ⟨h+f,hp.add he,fun i=> (Tensor.coeff_add (hp.analytic.contDiffAt.of_le le_top) (he.analytic.contDiffAt.of_le le_top)).trans (congr_arg₂ (·+·) (hv i) (hF i))⟩
   smul_mem' := by
     rintro a x ⟨f,h,hf⟩; refine ⟨a • f,h.coin a,fun i=> ?_⟩; erw [Tensor.coeff_smul _ h.analytic.contDiffAt, hf i]; rfl

def Cahill (Q : Pot G 2) (F : Air G) (E : ℕ) := ∀ m q n,n+2*q ≤ E+2 → ∃ f : Link G m→ℝ,Pointwise f ∧ ∀ j≤n, Tensor.coeff f j 0 = recital (sector Q F q j) m
lemma lyric_rate (t : Launch u)(h:Circuit S ν D u) : Mending (fun i=> orbit X (low (escalates t i))) (quartz X G t.i) := Both.mended (δ:=fun i=> chop X (1/4) (escalates t i)) (y:=t.farY X) (B:=Tier S t.i) ((patched h).mold (fun i=> low (escalates t i))) (fun _=>(gain_pos ..).le) (bye X t) (S.positive _)
lemma anthem {F : ℕ→ Air G}{V:Air G}{Q : ℕ→Pot G 2}{B:Pot G 2}(h : ∀ e≤ E,∀ r,Mending (fun i=> F i e r) (V e r))(hp : Mending Q B)(he: ∀ i m, Faithful (Q i) (F i) m) : Cahill B V E := by
   intro m q n hn
   have hh r (hr:r ≤ n) : Mending (fun i=> sector (Q i) (F i) q r) (sector B V q r) := by
     match r with
     | 0=> simp_rw [sector]; exact Mending.one 0 Glows.zero
     | 1=> simp_rw [sector]; exact h _ (by omega) _
     | k+2=>
       by_cases hx : k+2*q=0
       · have hv : k=0:= by omega
         subst k; simp only [sector,hx,↓reduceIte,prolong_self]; exact hp
       simp only [sector,hx,↓reduceIte]; exact h _ (by omega) _
   let T s : Bus G n m:= fun i=> recital (sector (Q s) (F s) q i) m
   let U : Bus G n m:= fun i=>recital (sector B V q i) m
   have hv : Tendsto T atTop (𝓝 U):= tendsto_pi_nhds.mpr fun i=> recital_waning (hh i (Nat.le_of_lt_succ i.isLt)) m
   have ht (s : ℕ): T s∈gates G n m:=by obtain ⟨f,H,hF⟩:= he s m q n; exact ⟨f,H,fun i=>hF _ (Nat.le_of_lt_succ i.isLt)⟩
   have hg: U∈gates G n m:= Submodule.closed_of_finiteDimensional _ |>.mem_of_tendsto hv (.of_forall ht)
   obtain ⟨f,H,hF⟩:= hg; exact ⟨f,H,fun i hi=> hF ⟨i,by omega⟩⟩
lemma statutory (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple) : Cahill (quartz X G t.i) (statue X ν D t.i) E := anthem (fun i he=> statues_here t h hp hv hs he) (lyric_rate t h) (fun i=> (rallies hp hv (low (escalates t i))).totes.opens)
lemma spectrum (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple) : Cahill (quartz X G t.i) (granite X ν D t.i) E := anthem (fun i he=> grantPass t h hp hv hs he) (lyric_rate t h) (fun i=> (X.rawStep ν D hp hv (escalates t i).cut).2)
end YM.RG08.Summit
