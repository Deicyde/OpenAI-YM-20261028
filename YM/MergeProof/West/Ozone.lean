import YM.MergeProof.North.Economist
import YM.MergeProof.West.Fur
import YM.MergeProof.West.Puppy
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Filter Set Function MeasureTheory Analysis Extraction Table Ward Climb Cells Next.UVStress Wilson Lattice Around Accent Ribbons
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{n:ℕ}(W:DiffPlan S)
variable (hC:C.Makes)(hq:Cells.CellHyp C F)(ho:F.PointLimits C S)(H:S.Hierarchy)
variable {ι:Type*}[Fintype ι](X:ι→Watch C) (w: (i:ι)→Fin ((X i).n+1)→ S.Tag) (g:ι→ℂ)
set_option quotPrecheck false
local notation "R" => fun i:ℕ=> fuga C.path.levels (i+1)
local notation "L" => C.path.levels
variable {d h D:ℕ}
structure Aroma (C:Family G):Prop where
   shells : Economics C
   opens : Stock.Tabs C.path.levels
   notes : Note C.S (fun i:ℕ=> fuga C.path.levels (i+1)) (-1)
include hC ho hq H
lemma zone (hp:W.Derivatives S)(hv:Aroma C) -- fix
    (hh:D+h=d+4)(B: S.Field 4)(T:S.Field d) (ht:∀ v:S.Field D,(∑ i:ι,g i*(X i).tester S D v)=0) {ε:ℝ}(hε:0<ε) :∀ᶠ m in atTop,∀ y∈annulus ((R) m), ‖∑ i:ι,g i*((((R) m):ℂ)^h * (X i).asked B T y)‖ ≤ ε:=by
   let b:= S.representative 4 B; let v:= S.representative d T
   have hb:S.project 4 b=B:= S.rep ..; have hT: S.project d v=T:= S.rep ..
   let Q:= Finset.univ.sup (fun i=>(X i).t); obtain ⟨k₀,hk⟩:=Stock.Tabs.mayOpen L 1 hv.opens Q
   let k:=max k₀ (C.ref D); have hK:Stock.Tabs.opens L 1 Q k:=Stock.Tabs.open_later _ _ hv.opens hk (le_max_left ..) zero_le_one
   obtain ⟨A,hA,hP⟩:= stencil_pay hC hq ho H X g Q (fun i=> Finset.le_sup (s:=Finset.univ) (f:=fun i=>(X i).t) (Finset.mem_univ i)) ht
   obtain ⟨s,j,hs,hj,hJ,hf⟩:=hv.shells.fees d D h hh
   let u(i:ι):Fin ((X i).n+1)→ S.Tag:= Fin.cons ⟨d,T⟩ (S.classTokens ∘ (X i).q)
   obtain ⟨n,hm⟩:= mountain W hC hq ho H ⟨4,B⟩ X u g hv.notes hp j s hs hj hJ h
   obtain ⟨P,hπ,hp⟩:= mars n
   let z:= ε/P; have hz:0<z:= div_pos hε hπ; let c:= stakes C Q k
   let a m:= C.S.a (j m)
   have he:Tendsto (fun m:ℕ=>2*(c/pitts C m)*A) atTop (𝓝 0):=by
       have h':Tendsto (pitts C) atTop atTop:= Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop (by norm_num) C.S.divergent)
       simpa only [mul_zero,zero_mul] using ((tendsto_const_nhds (x:=c)).div_atTop h'|>.const_mul (2:ℝ)).mul_const A
   have hx: Note C.S (fun m=>arm n*a m) (-s):= ((Note.notes C.S _ (arm_pos n)).mills ((Note.note_a C.S).relay j hj hJ)).swapP (by ring)
   have hw:∀ᶠ m in atTop, arm n*a m≤ (R) m /128:= hx.outweigh (hv.notes.splits (Note.notes C.S 128 (by norm_num))) (by linarith)
   filter_upwards [hw,he.eventually (ge_mem_nhds hz),hf Q k hK (le_max_right ..) v b F,eventually_all.mpr fun i=> cloudW (X i) hv.notes, hm z hz] with m hM he hh hc hr y hy
   let f:=district ⟨4,B⟩ X u g h m
   change ‖f y‖ ≤ ε
   refine (hp ((R) m) (a m) z (C.S.a_pos _) hz hM f (fun x hx ha=>?_) hr y hy).trans_eq (div_mul_cancel₀ ε hπ.ne')
   obtain ⟨x',rfl,hx'⟩:= read_grid (C:=C) ha
   specialize hP d h v b m (j m) _ hh _ hx (fun i=> hc i _ _ hx hx'); rw [hT,hb] at hP
   exact hP.trans he
end YM.MergeProof.Acme
