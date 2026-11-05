import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Rove
/-! # Window subgraph. Include halo physical condition on both endpoints (ANY).
 No local inverse prices from dimension strict only.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Stellar
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X')
local notation "B" => radiusB p

include hC he
lemma finish_point (b : Bond F) : ends (S) (curr (L).high.cut b)= (ends (Y) b).image (L).low.cut := by
  let L':= L; unfold ends pinPos; simp only [image_insert,image_singleton, curr,Prod.map_fst,Prod.map_snd,id_eq]; congr 1
  · exact L'.position b.1
  have hp:= L'.high.step_up b.1 b.2; refine congr_arg (singleton (β:=Finset _)) ?_; rw [← hp]; exact L'.position ..

include A
lemma length : 2*((B)+2)<c.val:=by have hp:= A.news; omega
lemma loyal (i j : Tubular F G) : i∈X'.shutter.take j → separation (along (Y) i) (along (Y) j) ≤ (B)+2 := fun hh=> A.D.1 ▸ (X'.shutter.high i j hh)
lemma grades (i j : Tubular F G) (hp : separation (along (Y) i) (along (Y) j) ≤(B)+2) :
    i∈X'.shutter.take j ↔ seed (L) i∈X.shutter.take (seed (L) j) := by
  unfold Coat.shutter; rw [in_frame,in_frame,A.D.1,A.D.2,show (seed (L) i).1=curr (L).high.cut i.1 from rfl,show (seed (L) j).1=curr (L).high.cut j.1 from rfl, finish_point (hC:=hC), finish_point (hC:=hC)]
  constructor
  · rintro ⟨x,hx,y,hy,h⟩; exact ⟨_,mem_image_of_mem _ hx,_,mem_image_of_mem _ hy,(less (divides hC) ..).trans h⟩
  rintro ⟨x,hx,y,hy,hp'⟩; obtain ⟨x,hx',rfl⟩:=mem_image.mp hx; obtain ⟨y,hy',rfl⟩:=mem_image.mp hy; refine ⟨x,hx',y,hy',?_⟩; have he : 2*separation x y<c.val:= by
    let f:= along (Y) i; let g:= along (Y) j
    have hh:separation x f≤1:= stride _ hx'; have hz:separation g y≤1:=by rw [separation_comm]; exact stride _ hy'
    change separation f g ≤ B+2 at hp
    have ha:=separation_triangle x f y; have hv:=separation_triangle f g y; have hh:= A.news; omega
  exact (teaches _ x y he).trans_le hp'
lemma derby (j:Tubular F G) : ∃ g: ↥(X'.shutter.take j)≃ ↥(X.shutter.take (seed (L) j)),∀ i, (g i).val=seed (L) i.val := by
  let l:=L; let W:=X'.shutter.take j; let J:=X.shutter.take (seed l j)
  let g (i:↥W):↥J:= ⟨seed l i.val,(A.grades _ j (A.loyal i j i.2)).1 i.2⟩
  have hc:= tempnest (G:=G) (H:=H) (h:=h) (Q:=Q) hC he
  have hj:Injective g:= fun i k hh=> Subtype.ext (hc.point A.length (along (Y) j) i.val k.val (by rw [separation_comm]; exact A.loyal i j i.2) (by rw [separation_comm]; exact A.loyal k j k.2) (congr_arg Subtype.val hh))
  have hk:Surjective g:= by
    intro i; obtain ⟨t,ht,hp⟩:= hc.esc (along (Y) j) i.val
    rw [hc.footing] at hp; have hv:= X.shutter.high i.val (seed l j) i.2; rw [A.D.2] at hv
    rw [separation_comm (along (Y) j),separation_comm (along (S) _)] at hp
    have hl : t∈ W:= (A.grades t j (hp.trans_le hv)).2 (ht.symm ▸ i.2); exact ⟨⟨_,hl⟩,Subtype.ext ht⟩
  exact ⟨Equiv.ofBijective g ⟨hj,hk⟩,fun i=>rfl⟩

lemma prospers (j:Tubular F G) (x : ↥(X'.shutter.take j)≃ ↥(X.shutter.take (seed (L) j))) (hx: ∀ i,(x i).val=seed (L) i.val) :
    X'.shutter.principal X'.plate j = (X.shutter.principal X.plate (seed (L) j)).submatrix x x := by
  ext i k; change X'.plate i.val k.val = X.plate (x i).val (x k).val; simp_rw [hx]; have hp:= A.news
  apply A.plank (2*(B+2)) (by omega) (by omega)
  have hy:= A.loyal i j i.2; have hv:=A.loyal k j k.2
  refine (separation_triangle _ (along (Y) j) _).trans ?_; rw [separation_comm (along (Y) j)]; omega
lemma echoes (i j:Tubular F G) (hp : separation (along (Y) i) (along (Y) j) ≤ B+2): X'.kernelA i j=X.kernelA (seed (L) i) (seed (L) j):= by
  by_cases hv : i∈X'.shutter.take j
  · obtain ⟨f',hF⟩:=A.derby j
    let I : ↥(X'.shutter.take j):=⟨i,hv⟩; let V: ↥(X'.shutter.take j):=⟨j,X'.shutter.here j⟩; let j':=seed (L) j
    rw [kernelA, kernelA, show X'.shutter.pad X'.plate i j=_ from X'.shutter.inside _ j I,A.prospers j f' hF, Matrix.inv_submatrix_equiv]; change (X.shutter.principal X.plate j')⁻¹ (f' I) (f' V)= X.shutter.pad X.plate _ _; rw [← (show (f' I).val=_ from hF I), X.shutter.inside]; apply congr_arg (fun t:↥(X.shutter.take j')=> (X.shutter.principal X.plate j')⁻¹ (f' I) t); exact Subtype.ext (hF V)
  rw [kernelA, kernelA, X'.shutter.outside _ _ _ hv, X.shutter.outside X.plate _ _ (fun h=>hv ((A.grades _ _ hp).2 h))]
lemma upright (hd : 2*D'<c.val) (i j:Tubular F G) (hp:separation (along (Y) i) (along (Y) j)≤ D'):
    X'.kernelA i j=X.kernelA (seed (L) i) (seed (L) j):= by
  by_cases hv:separation (along (Y) i) (along (Y) j)≤B+2
  · exact A.echoes i j hv
  have hx:= tempnest (G:=G) (H:=H) (h:=h) (Q:=Q) hC he; have hh:= teaches (divides hC) (along (Y) i) (along (Y) j) (lt_of_le_of_lt (Nat.mul_le_mul_left 2 hp) hd)
  unfold kernelA; rw [X'.shutter.thin _ _ _ (A.D.1.symm ▸ lt_of_not_ge hv), X.shutter.thin _ _ _ (A.D.2.symm ▸ lt_of_not_ge (by rw [hh,hx.footing,hx.footing] at hv; exact hv))]
lemma floor_c (p : Tubular F G): X'.driftM p=X.driftM (seed (L) p):= by
  unfold driftM; simp only [Pi.neg_apply,Matrix.mulVec,dotProduct,transpose_apply]; congr 1
  have H' := tempnest (G:=G) (H:=H) (h:=h) (Q:=Q) hC he; apply H'.all _ (along (Y) p) A.length
  · intro i hi; rw [separation_comm] at hi; rw [kernelA,X'.shutter.thin _ _ _ (by rw [A.D.1]; exact lt_of_not_ge hi),zero_mul]
  · intro i hi; rw [H'.footing,separation_comm] at hi; rw [kernelA,X.shutter.thin _ _ _ (by rw [A.D.2]; exact lt_of_not_ge hi),zero_mul]
  intro j hj; rw [separation_comm] at hj; rw [A.echoes _ _ hj,A.caput]
lemma mus : X'.μ= Deck.light (L).high.cut X.μ:= by ext x i; exact A.floor_c (x,i)
lemma allocates (hd : 2*D'<c.val) (i j : Tubular F G) (hp:separation (along (Y) i) (along (Y) j)≤D') :
    X'.relating i j=X.relating (seed (L) i) (seed (L) j):= by
  change _ * (X'.kernelA i j+X'.kernelA j i)= _ * (_+_) -- explicit
  rw [A.upright hd _ _ hp,A.upright hd _ _ (by rw [separation_comm]; exact hp)]; rfl
end YM.PhysicalNext.Repeat.Deck.Stellar
