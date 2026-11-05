import YM.RG08.Weald.Winch
import YM.RG08.Wisp.Carry
import YM.RG08.Quarry.School

/-!
# Cover Ward from regulator and reverse with all potentials/nav-parameters in local FPS.
Test deriv cost arbitrary and real profile (integrated evaluation);
this currency carries nonlinear gauge all coupling coefficients simultaneously.

Each marker has source weight integer cap l† from column. Full invariant kernels
`Calls` tested on compact-support probes in their *own* rescaled link
coordinate (both link and node chart probes normalized by same g). Finite torus
reads arbitrary valuation FPS therefore follow even after reexpression. For
polynomial on cover, use separate extensions. d global DOESN'T need be
read as Taylor germ. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Weald
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open Room Gallery Camera MvPolynomial Glyph Quarry Stationary
open scoped Topology BigOperators ENNReal Classical PowerSeries
variable {G:Gauge}{l n d:ℕ}{I:Type}[Fintype I]
abbrev Ed (G:Gauge) (M:Type):= M×Loc G 1
abbrev Nd (G:Gauge) (M:Type):= M×G.ColorIndex
abbrev Plot (G:Gauge)(M:Type):= M × cuff G
variable {M:Type}
def paint (x : Ed G M→Dig)(b:Nd G M→Dig)(i:Plot G M):= Sum.elim (fun s=> x (i.1,s)) (fun s=> b (i.1,s)) i.2
def rend (d:G.El)(x : Plot G Cover→Dig)(i:Ed G Cover):Dig:=breath (x ∘ jab (hot d) i) (eye ((hot d).fare i.2))
lemma rend_zero (d:G.El)(i:Ed G Cover):rend d 0 i=0:=dark _
def gain (d:G.El)(x:Ed G Cover→Dig)(b:Nd G Cover→Dig):Ed G Cover→Dig:=rend d (paint x b)

-- i≥0 in canonical labels as before. include rank0.
def Calls (l:ℕ)(P:GrainS (Ed G Cover)):Prop:=∀ f:Pearl,∀ (x:Tray (Ed G Cover))(b:Tray (Nd G Cover))(d:G.El),mint l P f x=mint l P f (portrait (hot d) (art x b))

def trim {A:Type}(s:Finset A)(a:A→Dig):Tray A:=⟨s,fun i=> if i∈s then a i else 0,fun _ hi=>if_neg hi⟩
variable {P:GrainS (Ed G Cover)}
lemma relax (he:Calls l P)(hp:Pops P)(x:Ed G Cover→Dig)(b:Nd G Cover→Dig)(d:G.El)
 (hx:Safe x)(hb:Safe b)(f:Pearl):awaken l P f x=awaken l P f (gain d x b):=by
 let A:=Ed G Cover;let Y:=Nd G Cover
 let R:= Finset A×Finset Y
 let a(s:R):=trim s.1 x;let u(s:R):=trim s.2 b
 have hh (s:R):mint l P f (a s)=mint l P f (portrait (hot d) (art (a s) (u s))):=he ..
 let s (q:R):= (a q).get;let t (q:R):=(u q).get
 have H(q:R):awaken l P f (s q)=awaken l P f (gain d (s q) (t q)):=by rw [show gain d (s q) (t q)=(portrait _ (art (a q) (u q))).get from rfl,woken,woken];exact hh q
 have hs:Safe (fun i:R×A=>s i.1 i.2):=fun k=>by obtain ⟨C,hc,H⟩:=hx k; refine ⟨C,hc,fun i=>?_⟩; dsimp only [s,a,trim]; split; exact H _; simp [tap,hc]
 have ht:Safe (fun i:R×Y=>t i.1 i.2):=fun k=>by obtain ⟨C,hc,H⟩:=hb k; refine ⟨C,hc,fun i=>?_⟩; dsimp only [t,u,trim]; split; exact H _; simp [tap,hc]
 have ha(i:A):∀ᶠ (q:R) in atTop,s q i=x i:=by
    filter_upwards [eventually_ge_atTop (({i},∅):R)] with q hq
    exact if_pos (show i∈q.1 from hq.1 (mem_singleton.mpr rfl))
 have hu(i:Y):∀ᶠ (q:R) in atTop,t q i=b i:=by
    filter_upwards [eventually_ge_atTop ((∅,{i}):R)] with q hq
    exact if_pos (show i∈q.2 from hq.2 (mem_singleton.mpr rfl))
 have hY:Safe (fun i:R×A=>gain d (s i.1) (t i.1) i.2):=by
    refine Safe.readers (J:=R×A) (A:=fun i=> paint (s i.1) (t i.1)) ?_ (fun i=>i.2.2) (fun i=>jab (hot d) i.2) (fun j=>eye ((hot d).fare j))
    intro k; obtain ⟨C,hc,Hc⟩:=hs k;obtain ⟨B,hy,HB⟩:=ht k
    refine ⟨C+B,add_nonneg hc hy,?_⟩;rintro ⟨⟨q,x⟩,i,v|v⟩
    · exact (Hc (q,(i,v))).trans (le_add_of_nonneg_right hy)
    exact (HB (q,(i,v))).trans (le_add_of_nonneg_left hc)
 have hd(i:A):∀ᶠ q:R in atTop,gain d (s q) (t q) i= gain d x b i:=by
    let g:=jab (hot d) i
    let z:= paint x b
    have he(v:foil G):∀ᶠ q:R in atTop,paint (s q) (t q) (g v)=z (g v):=by rcases hi:g v with ⟨i,p|p⟩;exact ha _;exact hu _
    filter_upwards [eventually_all.mpr he] with q hq
    exact congrArg (fun (u:foil G→Dig)=> breath u (eye ((hot d).fare i.2))) (show paint (s q) (t q) ∘ g=z ∘ g from funext hq)
 ext k:1; change tap k _=tap k _
 have hT:=flatish (l:=l) P hp f hs ha k
 have hB:=flatish (l:=l) P hp f hY hd k
 exact tendsto_nhds_unique hT (by simp_rw [←H] at hB;exact hB)

-- Define torus rotated & dependence. clearance not needed since folding all tapes.
def route (P:Side)(g:G.El)(y:Plot G (Site P)→Dig)(i:Ed G (Site P)):Dig:=breath (y ∘ dodge (hot g) i) (eye ((hot g).fare i.2))
def own {Q:Side}(g:G.El)(i:Ed G (Site Q)):Port (Plot G (Site Q)):= belt (fun j=>rod (dodge (hot g) i j)) (eye ((hot g).fare i.2))
lemma owned {Q:Side} (g:G.El)(i:Ed G (Site Q))(x:Plot G (Site Q)→Dig):breath x (own g i)=route Q g x i:=by rw [own,fugue];simp_rw [bases_x];rfl
-- torus stock
lemma period_wednesday (he:Calls l P)(hp:Pops P)(Q:Side)(f:Pearl)(g:G.El)(x:Plot G (Site Q)→Dig):
 let V:=Trickle.mark l (fun i n=>Hatch.broom (port Q) (P i n)) f
 ; breath (fun i:Ed G _=>x (i.1,Sum.inl i.2)) V=breath (route Q g x) V:=by
 intro V
 let U:Plot G Cover→Dig:=x ∘ port Q
 let X(i:Ed G Cover):= U (i.1,.inl i.2); let Y(i:Nd G Cover):= U (i.1,.inr i.2)
 have ht:Safe U:=fun k=>⟨∑ i:Plot G (Site Q),|tap k (x i)|,Finset.sum_nonneg (fun _ _=>abs_nonneg _),fun i=>Finset.single_le_sum (f:=fun i:Plot G (Site Q)=> |tap k (x i)|) (fun i _=>abs_nonneg _) (mem_univ (port Q i))⟩
 have H:=relax he hp X Y g (ht.take _) (ht.take _) f
 have hx: gain g X Y=(route Q g x) ∘ port Q:=by
    funext i; apply congrArg (fun u:foil G→Dig=> breath u (eye ((hot g).fare i.2)))
    funext j
    unfold paint X Y U Quarry.dodge Quarry.jab Function.comp Isles.port
    rcases h:(hot g).offset i.2 j with ⟨z,k|k⟩ <;> simp only [map_add,h,Sum.elim_inl,Sum.elim_inr]
 unfold V; rw [hat,hat,broomAwake (ht:=?_), broomAwake (ht:=?_),←hx];exact H
 all_goals intro e n;obtain ⟨hy,L,d,b,u,C,hV⟩:=hp e n;exact ⟨L,d,b,u,C,hy,hV⟩

/-- Ward at finite regulator on arbitrary analytic precursor, here external
and gauge parameter cells as Port-linearized variables around trivial orbit.
Therefore usable on any g-dependent group chart via composition. Don't skip taking the
normalized step before log. -/
theorem summer (he:Calls l P)(hp:Pops P)(Q:Side)(f:Pearl)(g:G.El):
 let V:=Trickle.mark l (fun i n=>Hatch.broom (port Q) (P i n)) f
 ; belt (fun i:Ed G (Site Q)=>Room.rod (i.1,Sum.inl i.2)) V=belt (own g) V:=by
 intro V;apply lamp;intro x; simp_rw [fugue,bases_x,owned];exact period_wednesday he hp Q f g _
end YM.RG08.Weald
