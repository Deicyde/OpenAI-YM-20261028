import YM.RG08.Spar.Recruit

/-!
# Intertwining from two period witnesses. No requirement all-period data; cofinal agreements
suffice also at higher arities because only finite curl reads have to pass to the limit
once Φ has been constructed. Take all tests on slots before color compression.
-/
noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG Rows
open scoped Topology BigOperators Classical ENNReal Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I J : Type}[Fintype I]{n:ℕ}{l u:ℕ→Side}

def climb (l:ℕ→Side):= Tendsto (fun m=>(l m).val) atTop atTop
omit [Fintype I] in
lemma chain_eye {F:Flake n (Market I)}{K:ViewDeck n I}(_h:Eyes K F)(_he:climb l)(x:Tape n (Market I)) :
 let _f (c:Side) (_y:Tape n (Co c I)):= True
 Tendsto (fun _m : ℕ => F x) atTop (𝓝 (F x)):=by
 intro _
 exact tendsto_const_nhds
omit [Fintype I] in
lemma cofinal {K:Flake n (Market I)}(hc:Cohort K)(θ C:ℝ)(he:0<θ)(hp:0≤C)(h:Held (carpet I) θ C K)(i:Fin n)(ht:climb l)(x:Tape n (Market I)):
 Tendsto (fun m=>pour K i (port (l m) ∘ x)) atTop (𝓝 (K x)):=by
 let N(m:ℕ):=(l m).val-1;have hn:Tendsto N atTop atTop:= tendsto_atTop.mpr fun b=> (ht.eventually (eventually_ge_atTop (b+1))).mono fun m hm=>by change b+1≤(l m).val at hm;unfold N;omega
 have hr(m):chain (N m)=l m:=Subtype.ext (by have hz:=(l m).pos;change (l m).val-1+1=(l m).val;omega)
 have H:= ((bureau hc h he hp i).light (Fin.pos i) x).comp hn
 exact H.congr' (Eventually.of_forall fun m=>congr_arg (fun P:Side=>pour K i (port P ∘ x)) (hr m))

lemma tilt_stencil {Q:Flake n (Market I)}{K:Kernel I J}{σ C v D:ℝ}(S:∀ m,StepData (l m) (u m)){A:(m:ℕ)→Matrix (Co (u m) I) (Co (l m) J) ℝ}
    (ht:climb l)(i:Fin n){L:Side}(hL:∀ m,(S m).patch.L=L)
    (hT:Cohort Q)(hp:0≤C)(he:Held (carpet I) v C Q)(hσ:0<σ)(hv:σ≤L.val*v)(HK:Priced σ D (clover L K))(hm:∀ m,Matches K (A m)) (x:Tape n (Market J)):
    Tendsto (fun m=>query (A m) (pour Q i) (port (l m) ∘ x)) atTop (𝓝 (braces K Q x)):=by
 rw [← braces_farm (L:=L)]
 let M (m:ℕ):Matrix (Co (l m) (Co L I)) (Co (l m) J) ℝ:= (show (S m).patch.L=L from hL m) ▸ Matrix.of (fun w z=>A m ((splitCo (S m).ratio I).symm w) z)
 have hX(m:ℕ){L:Side}(H:(S m).patch.L=L) :
    let X:Matrix (Co (l m) (Co L I)) (Co (l m) J) ℝ:=H ▸ Matrix.of (fun w z=>A m ((splitCo (S m).ratio I).symm w) z)
    Matches (clover L K) X ∧ ∀ y:Tape n (Cove (l m) J), query X (pour (farm L Q) i) y=query (A m) (pour Q i) y:=by
    subst H;intro X; refine ⟨clover_match (S m) (hm m),?_⟩
    intro y
    unfold query
    let E:=carton n _ _ ((splitCo (S m).ratio I).symm)
    rw [←Equiv.sum_comp E (fun x=>pour Q i x*∏ j,A m (x j) (y j))];apply sum_congr rfl;intro z _;rw [farmed hT (S m)];rfl
 have H (m:ℕ)(y:Tape n (Cove (l m) J)): query (A m) (pour Q i) y=query (M m) (pour (farm L Q) i) y:= ((hX m (hL m)).2 y).symm
 simp_rw [H]
 -- Each evaluation uses just the labels of the fixed output tape.
 let Kx : Kernel (Co L I) (Fin n) := fun a y => clover L K a (y.1, (x y.2).2)
 let Ax (m : ℕ) : Matrix (Co (l m) (Co L I)) (Co (l m) (Fin n)) ℝ :=
   fun a y => M m a (y.1, (x y.2).2)
 have hKx : Priced σ D Kx :=
   ⟨HK.pos, fun a y v => HK.city a (y.1, (x y.2).2) v,
     fun a j => HK.row a (x j).2, fun a y => HK.col a (y.1, (x y.2).2)⟩
 have hAx (m : ℕ) : Matches Kx (Ax m) :=
   fun z y => (hX m (hL m)).1 z (y.1, (x y.2).2)
 exact suppliesSeen ht i hσ hKx (show 0 ≤ C * Real.exp (8*σ) by positivity)
   (farm_path hT) (farm_cost hσ.le hv he hp) hAx (fun j => ((x j).1, j))
end YM.RG08.Spar
