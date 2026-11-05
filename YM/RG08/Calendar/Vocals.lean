import YM.RG08.Calendar.Basis
import YM.RG08.Lyt.Axis
/-!
 # Finite words and spectra for one-mark & multi Fk operations, fixed R.
 All test functions arbitrary C^D (orders as stipulated in the use contexts).
 k purchased for pol repetitions; may also use Tin widths.
 Cluster mixed root algebra paid up to Fin n, *not* a bound in n.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Admission
open Function Filter Lattice Wilson Exterior Precision Laurent Finset RG Next.Free RG.Supply Bloch Input Conductor Wings Stationary Staffer Drift Virtue
open Town Run Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Creek
open scoped BigOperators Topology Real Classical
variable {I H:Type} {G:Gauge}{K:KernelChoices}

-- tickets allow arbitrary radius explicitly on consumer. For builder charge on
-- the countable list of cell cubes with half-side R=1/2+a_nat/2, containing
-- every physical cell request. (Often R=1/2 precisely.) Mark array dimension bounded
-- by n, heights with FULL BASIS for EVERY d≤D field horizon charged separately.
structure Ask where
   n : ℕ
   E : ℕ
   max_h : ℕ
   a : ℕ -- extra sheets radius
   tests : ℕ -- integer support derivatives extra > max
   jet : ℕ -- valuation margin
   mom : ℕ -- extra pol trajectory/contact factors
   vac : ℕ -- analytic extra packets of support

namespace Ask
instance : Encodable Ask:= Encodable.ofLeftInjection (fun k=>(k.n,k.E,k.max_h,k.a,k.tests,k.jet,k.mom,k.vac)) (fun t:ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×ℕ=>some ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2.1,t.2.2.2.2.2.2.1,t.2.2.2.2.2.2.2⟩) (fun _=>rfl)
def R (k:Ask) : ℝ := ((k.a+1:ℕ):ℝ)/2
def D (k:Ask) := k.max_h+1+k.tests
def τ (k:Ask) := k.max_h+k.jet
def fine (k:Ask) := k.max_h*k.max_h*(k.τ+k.E)+k.max_h+1+k.mom
lemma Rhalf (k:Ask):1/2≤ k.R := by unfold R; gcongr; norm_cast; omega
lemma Dplus (k:Ask)(i:Fin (k.max_h+1)): i.val+1≤ k.D:= by unfold D; omega
lemma dh (k:Ask)(i:Fin (k.max_h+1)): i.val≤ k.τ:= by unfold τ; omega
lemma tests_take (k:Ask)(i:Fin (k.max_h+1)): i.val+1≤ k.fine:= by unfold fine; omega
lemma bills_take (k:Ask)(i:Fin (k.max_h+1)): i.val*i.val*(k.τ+k.E)≤ k.fine:= by
   have hp: i.val ≤ k.max_h:= by omega
   unfold fine; refine le_trans ?_ (show k.max_h*k.max_h*(k.τ+k.E) ≤_ by omega); gcongr
lemma numbers (E n r h k l d t:ℕ) : ∃ x:Ask,x.n=n ∧ x.a=r ∧ x.E=E ∧ x.vac=h ∧ k ≤ x.fine ∧ l≤ x.τ ∧ d ≤ x.D ∧ t ≤ x.max_h := by
   let x:Ask:= ⟨n,E,t,r,d,l,k,h⟩; refine ⟨x,rfl,rfl,rfl,rfl,?_,?_,?_,le_rfl⟩ <;> dsimp [Ask.fine,τ,D,x] <;> omega
end Ask

variable {C':Frames G}{P:Hol G}{Ω:∀ i,SectionData (C'.level i)}
abbrev Lineage (P:Hol G)(Ω:∀ i,SectionData (C'.level i))(B:Names G K)(a:Ask)(i:Fin (a.max_h+1)):= Signals B.fund B.cov a.E a.τ P (Ω i) a.Rhalf (a.Dplus i)

structure Dialect (P:Hol G)(Ω:∀ i,SectionData (C'.level i))(B:Names G K) (a:Ask) where
   clear : Grotto G B.fund a.fine a.E a.τ
   factory (i:Fin (a.max_h+1)) : Lineage P Ω B a i
   heights (i:Fin (a.max_h+1)): Aperture G B.fund a.fine a.E a.τ i a.D a.R
   w : ℕ→ℝ
   soft (i:Fin (a.max_h+1)) : Lineage P Ω B a i
   small (i) : (soft i).wi=w
   hp i j: w j ≤ secretT (factory i) (Fin a.n) j
   gates (i : Fin (a.max_h+1)) : ℕ→ℕ
   able (v i j) (F:Flight j i) : gates v j ≤ F.L.val →(factory v).wi i ≤ F.L.val*w j
lemma Dialect.rain {N:Names G K}{a:Ask}(b:Dialect P Ω N a)(i:ℕ): 0< b.w i:= by rw [← b.small 0]; exact (b.soft 0).pos _
lemma Dialect.lower {N:Names G K}{a:Ask}(b:Dialect P Ω N a)(i j):b.w j ≤ (b.factory i).wi j:= by
     let F:= b.factory i; exact (b.hp _ _).trans ((le_mul_of_one_le_left (secret_t F (Fin a.n) j|>.le) (by norm_num : (1:ℝ)≤ 2)).trans (secret_l ..))
lemma wishes (h:∀ i,(Ω i).Sound P)(hp:∀ i,Bid.pop (Ω i))(B:Names G K)(a:Ask): Nonempty (Dialect P Ω B a) := by
     let b (i:Fin (a.max_h+1)):= Classical.choice (orient P B.fund B.cov a.τ a.E a.Rhalf (a.Dplus i) (h i) (hp i))
     let w j:= ((∑ i,(secretT (b i) (Fin a.n) j)⁻¹)+(1:ℝ))⁻¹; have hw j: 0<w j:= inv_pos.mpr (add_pos_of_nonneg_of_pos (sum_nonneg fun i _=>inv_nonneg.mpr (secret_t .. |>.le)) zero_lt_one)
     have he i j:w j ≤ secretT (b i) (Fin a.n) j:=by
        have hQ:= secret_t (b i) (Fin a.n) j
        apply (inv_anti₀ (inv_pos.mpr hQ) ?_).trans_eq (inv_inv _)
        exact (single_le_sum (s:=univ) (f:=fun i=> (secretT (b i) (Fin a.n) j)⁻¹) (fun i _=>inv_nonneg.mpr (secret_t .. |>.le)) (mem_univ i)).trans (le_add_of_nonneg_right zero_le_one)
     have ht i j:w j ≤ (b i).wi j:= (he i j).trans ((le_mul_of_one_le_left (secret_t .. |>.le) (by norm_num : (1:ℝ)≤2)).trans (secret_l ..))
     choose Q hQ using fun i=>brook_gates hw (b i).wi
     choose W hW _ _ using fun i=>Lyt.narrow_l (b i) w hw (ht i)
     exact ⟨⟨Classical.choice (bears B.fund G a.fine a.τ a.E),b,fun i=> Classical.choice (prepareA G B.fund _ _ _ _ _ (a.tests_take i) (a.Dplus i) (a.bills_take i) a.Rhalf),w,W,hW,he,Q,hQ⟩⟩

variable {N:Names G K}{a:Ask}
def offers (i:Fin (a.max_h+1))(A:Lineage P Ω N a i):Need:= ⟨A.gate, fun j i _ _=> max ((A.wi i)⁻¹) (A.cost j i)⟩
def consents (b:Dialect P Ω N a): Need:= Need.brings (⟨b.clear.gate,fun _ _ _ _=>0⟩:Need) (Need.basket fun i=>(Need.brings (⟨fun j=> max ((b.heights i).gate j) (b.gates i j),fun _ _ _ _=>0⟩: Need) (Need.brings (offers (N:=N) (Ω:=Ω) (a:=a) i (b.factory i)) (offers (N:=N) (Ω:=Ω) (a:=a) i (b.soft i)))))

variable {X:Levels G} {D:ChartRatio G}{ν:G.ColorIndex}{B:Names G X.clock.kernel}{b:Dialect P Ω B a} {u:H→Windows}
local notation "ξ"=> Chain.actual X
private lemma enabled_at (ht:G.Simple)(i:Fin (a.max_h+1))(A:Lineage P Ω B a i)(hv:NearZ X u)(he:∀ k,i.val+2≤ X.clock.J (u k).start)(hb:∀ k,Affords (offers (N:=B) (a:=a) (Ω:=Ω) i A) X (u k).start): Enabled (X:=ξ) A u:=
     ⟨he, fun t=> (hb t.b).lo _ t.geC, Affords.cash_w ht hv hb (fun i=> inv_nonneg.mpr (A.pos _).le) (fun i=>le_max_left ..), Affords.cash_w ht hv hb (fun i=>zero_le_one.trans (A.admits ..)) (fun i=>le_max_right ..)⟩
structure Lights (b:Dialect P Ω B a)(u:H→Windows)(ν:G.ColorIndex)(D:ChartRatio G): Prop where
   permanent (i): Tights (X:=ξ) (b.factory i) (B.act a.E) ν D u
   closer (i): Tights (X:=ξ) (b.soft i) (B.act a.E) ν D u
   plume (i): BrookW (X:=ξ) (b.factory i) u (Fin a.n) b.w
   led : Pines (X:=ξ) b.clear u
   stretch (i) : Heirs (X:=ξ) (b.heights i) u
lemma loaded (h:∀ i,(Ω i).Sound P)(hp:∀ i,Bid.pop (Ω i))(g:G.Simple)(hd: LocalRatio D)(hv:NearZ X u)(he:∀ k,a.max_h+2≤ X.clock.J (u k).start)(hc:∀ k, Affords (consents b) X (u k).start)(hB:Ball B D ν u a.E a.vac): Lights b u ν D:= by
    have hx i k:= Need.basket_affords _ ((hc k).of_sub (Need.Higher.back ..)) i -- reduce type
    have hh (i:Fin (a.max_h+1)) k:i.val+2 ≤ X.clock.J (u k).start := (show i.val+2 ≤ _ from (by omega): i.val+2 ≤ a.max_h+2).trans (he k)
    let A i:= hx i
    have hs i:= enabled_at (B:=B) g i (b.soft i) hv (hh i) (fun k=> ((hx i k).of_sub (Need.Higher.back ..)).of_sub (Need.Higher.back ..))
    refine ⟨fun i=>⟨hB.yes,enabled_at g i (b.factory i) hv (hh i) (fun k=> ((hx i k).of_sub (Need.Higher.back ..)).of_sub (Need.Higher.front ..)), a.dh i,g,Chain.wake_actual X,hd,h i,hp i⟩,fun i=>⟨hB.yes,hs i,a.dh i,g,Chain.wake_actual _,hd,h _,hp _⟩,fun k=>⟨b.rain,b.hp _,fun t=>?_,?_⟩,⟨fun t=>?_⟩,fun k=>⟨fun t=>?_,fun t=>(hh k t.b).trans (X.fits.mono (t.geC.trans (Nat.le_succ t.i)))⟩⟩
    · apply b.able _ _ _ ((Chain.actual X).step t.i (.top _)) ((le_max_right ..).trans (((hx k t.b).of_sub (Need.Higher.front ..)).lo _ t.geC))
    · rw [← b.small 0]; exact (hs 0).costs
    · exact ((hc t.b).of_sub (Need.Higher.front ..)).lo _ t.geC
    exact (le_max_left ..).trans (((hx k t.b).of_sub (Need.Higher.front ..)).lo _ t.geC)
end YM.RG08.Admission
