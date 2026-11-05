import YM.MultipleContact.Multi.Parcel
/-! Dynamic estimates against one fixed detector probe schedule. -/

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.MultipleContact.ScheduleRow
open Filter Set Function MeasureTheory Extraction Table Ward MergeProof Ribbons Cells Next.UVStress Wilson Lattice Arbor
open Script Scene Bunching
open RG Bunching.Cord
open Drama
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}
variable {n h:ℕ}[Inhabited (Fin n)] {v:Fin n → C.book.Token}{x:Fin n → Cover}{u:ℕ×ℕ → C.book.Ref h}{J M j:ℕ}{w A:ℝ}
variable {fl: Filter (ℕ×ℕ)} (hf:fl.NeBot) {xe:Fin n → E4}
variable (hA: Wage F C (Loss C (j:=j) x v w u) J A)
include hf hA
set_option maxRecDepth 100000
lemma probe_ticket (e:Exterior C.book)(A':Fin e.n → ℝ)(hB:∀ i:Fin e.n, Wage F C (Drama.Unit C ((e.letter i).2)) J (A' i))
   (hy:xe=C.S.gridPoint j ∘ x)(hX:∀ a:Axis, Injective (fun k:Fin n=>xe k a))(hsmall:∀ i,‖xe i‖ ≤ C.S.a M)
   {S:Table C.book}(HS:S.Hierarchy)(hm:F.PointLimits C S){g:C.book.Ref h}(hT: Tendsto u fl (𝓝 g))(hF: fl ≤ F.fuse)
   (hJ:M ≤ J) (hM: ((e.n+1:ℕ):ℝ)*(6*C.S.a J) < C.S.a M)(hfar:Drama.far (C.S.a M) (WithLp.ofLp e.point))(hc:C.Makes):
   ‖evaluation S (expression .signed w (S.classTokens ∘ v) (S.project _ g) (e.point 0) xe * prospect S e)‖ ≤ A * ∏ i:Fin e.n,A' i := by
   classical
   let d : Fin (e.n+1)→ℕ:=Fin.cons (α:=fun _=>ℕ) h (fun i=>(e.letter i).fst)
   let g' : Fin (e.n+1) → Mode:=Fin.cons (α:=fun _=>Mode) .signed (fun _=>.fused)
   let u'(t:ℕ×ℕ)(i:Fin (e.n+1)):C.book.Ref (d i):= i.cases (u t) (fun p=>(e.letter p).snd)
   let xe': Fin (e.n+1) → Fin n → E4:=Fin.cons (α:=fun _=>Fin n→E4) xe (fun _=>0)
   have HT: Tickets C F (fun _=>w) (fun _:Fin (e.n+1)=>v) u' g' J (fun _=>0) (fun _=>0) (fun _=>j) (fun _=>x) (fun _=>fun _:Fin n=>0) (Fin.cons (α:=fun _=>ℝ) A A') := by
      refine ⟨fun i h=> Fin.cases (motive:=fun i=>g' i=.signed → Wage F C (Loss C (d:=d i) (j:=j) x v w (fun t=>u' t i)) J (Fin.cons (α:=fun _=>ℝ) A A' i)) ?_ (fun j h=>(by cases h)) i h, fun i h=>Fin.cases ?_ (fun j _=> hB j) i h, fun i h=>(Fin.cases (motive:=fun i=>g' i=.raw → False) (fun q=>by cases q) (fun j q=>by cases q) i h).elim⟩
      · exact fun h=>hA
      · exact fun he=>by cases he
   let h₀ (i:Fin (e.n+1)): C.book.Ref (d i):= Fin.cases g (fun k=>(e.letter k).snd) i
   have hx:∀i,g' i=.signed → xe' i=(C.S.gridPoint j∘x):=fun i hi=> Fin.cases (motive:=fun k=> g' k=.signed → xe' k=_) (fun h=>hy) (fun j h=>by cases h) i hi
   have H := Drama.passage (s:=WithLp.ofLp e.point) (xe:=xe') HT HS hm hF (v0:=h₀) (fun i=>(by
        exact Fin.cases hT (fun j=>(by change Tendsto (fun _=>(e.letter j).snd) _ (𝓝 _); change Tendsto (fun _=>_) _ (𝓝 _);exact tendsto_const_nhds)) i)) hc hJ hM hfar hx (fun i hi=> Fin.cases (motive:=fun i=>g' i=.signed → ∀a:Axis,Injective (fun x=> (xe' i x) a)) (fun _=> hX) (fun j h=>by cases h) i hi) (show _ from ?_) (show _ from ?_)
   · convert H using 1
     · congr 2; rw [Fin.prod_univ_succ,Scene.prospect,spell]; congr 1
     rw [Fin.prod_univ_succ]; rfl
   · intro i h
     obtain ⟨k,hk⟩:=Fin.eq_succ_of_ne_zero (show i≠0 from by intro hx; rw [hx] at h; cases h); rw [hk] at h; cases h
   exact ⟨fun i=> Fin.cases (fun h=> fun s k h=> hX 0 (congr_arg (fun y:E4=>y 0) h)) (fun u h=>False.elim (h rfl)) i, (fun i=> Fin.cases hsmall (fun j k=>by simpa only [xe',Fin.cons_succ,Pi.zero_apply,norm_zero] using (C.S.a_pos _).le) i)⟩
end YM.MultipleContact.ScheduleRow
